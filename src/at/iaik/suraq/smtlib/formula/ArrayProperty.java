/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import at.iaik.suraq.exceptions.InvalidIndexGuardException;
import at.iaik.suraq.exceptions.InvalidValueConstraintException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.HashTagContainer;
import at.iaik.suraq.util.IdGenerator;
import at.iaik.suraq.util.ImmutableArrayList;
import at.iaik.suraq.util.Util;

/**
 * 
 * This class represents an array property. See the book of Bradley & Manna
 * "The Calculus of Computation" for more details on array properties.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayProperty implements Formula {

    /**
     * 
     */
    private static final long serialVersionUID = -1979830923087843951L;

    private final long id = IdGenerator.getId();

    /**
     * The collection of universally quantified variables.
     */
    private final ImmutableArrayList<DomainVariable> uVars;

    /**
     * The formula representing the index guard.
     */
    private final Formula indexGuard;

    /**
     * The formula representing the values constraint.
     */
    private final Formula valueConstraint;

    /**
     * 
     * Constructs a new <code>ArrayProperty</code> with the given values.
     * 
     * @param uVars
     *            the collection of universally quantified variables.
     * @param indexGuard
     *            the index guard.
     * @param valueConstraint
     *            the value constraint.
     * @throws InvalidIndexGuardException
     *             if the index guard does not adhere to the grammar
     * @throws InvalidValueConstraintException
     *             if the value constraint does not adhere to the grammar.
     */
    private ArrayProperty(Collection<DomainVariable> uVars, Formula indexGuard,
            Formula valueConstraint) throws InvalidIndexGuardException,
            InvalidValueConstraintException {
        this.uVars = new ImmutableArrayList<DomainVariable>(uVars);

        if (indexGuard instanceof FormulaTerm)
            indexGuard = ((FormulaTerm) indexGuard).getFormula();

        if (!ArrayProperty.checkIndexGuard(uVars, indexGuard))
            throw new InvalidIndexGuardException();

        if (valueConstraint instanceof FormulaTerm)
            valueConstraint = ((FormulaTerm) valueConstraint).getFormula();

        if (!ArrayProperty.checkValueConstraint(uVars, valueConstraint))
            throw new InvalidValueConstraintException();

        this.indexGuard = indexGuard;
        this.valueConstraint = valueConstraint;
    }

    public static ArrayProperty create(Collection<DomainVariable> uVars,
            Formula indexGuard, Formula valueConstraint)
            throws InvalidIndexGuardException, InvalidValueConstraintException {
        return (ArrayProperty) FormulaCache.formula.put(new ArrayProperty(
                uVars, indexGuard, valueConstraint));
    }

    /**
     * Checks whether the given formula is a legal value constraint (w.r.t. the
     * given universally quantified variables).
     * 
     * @param uVars
     *            a list of universally quantified variables
     * @param valueConstraint
     *            the formula to check
     * @return <code>true</code> if the given formula is a legal value
     *         constraint w.r.t. the given list of universally quantified
     *         variables, <code>false</code> otherwise.
     */
    private static boolean checkValueConstraint(
            Collection<DomainVariable> uVars, Formula valueConstraint) {

        if (valueConstraint instanceof BooleanCombinationFormula) {
            for (Formula subFormula : ((BooleanCombinationFormula) valueConstraint)
                    .getSubFormulas()) {
                if (!ArrayProperty.checkValueConstraint(uVars, subFormula))
                    return false;
            }
            return true;
        }

        if (valueConstraint instanceof DomainEq) {

            for (DomainTerm term : ((DomainEq) valueConstraint)
                    .getDomainTerms()) {
                if (term instanceof ArrayRead) {
                    DomainTerm index = ((ArrayRead) term).getIndexTerm();
                    if (!(index instanceof DomainVariable))
                        return false;
                } else {
                    if (!term.isEvar(uVars))
                        return false;
                }
            }
            return true;
        }

        // something that is not a legal value constraint
        return false;
    }

    /**
     * Returns a set of all terms used as eVars in the index guard.
     * 
     * @param uVars
     *            a collection of uVars.
     * @param indexGuard
     *            the index guard (or a subformula of it)
     * @return the set of all terms that parse as evars in the given
     *         <code>indexGuard</code>.
     * @throws InvalidIndexGuardException
     *             if the given <code>indgexGuard</code> is not a valid one.
     *             (This method does not perform all checks; the exception is
     *             merely thrown when an invalid index guard is found
     *             "by chance".)
     */
    private static Set<DomainTerm> getEVarsFromIndexGuard(
            Collection<DomainVariable> uVars, Formula indexGuard)
            throws InvalidIndexGuardException {
        if (indexGuard instanceof PropositionalConstant)
            // only "true" is allowed in index guards
            return new HashSet<DomainTerm>();

        if (indexGuard instanceof AndFormula) {
            Set<DomainTerm> result = new HashSet<DomainTerm>();
            for (Formula formula : ((AndFormula) indexGuard).getConjuncts())
                result.addAll(ArrayProperty.getEVarsFromIndexGuard(uVars,
                        formula));
            return result;
        }

        if (indexGuard instanceof OrFormula) {
            Set<DomainTerm> result = new HashSet<DomainTerm>();
            for (Formula formula : ((OrFormula) indexGuard).getDisjuncts())
                result.addAll(ArrayProperty.getEVarsFromIndexGuard(uVars,
                        formula));
            return result;
        }

        if (indexGuard instanceof DomainEq) {
            Set<DomainTerm> result = new HashSet<DomainTerm>();
            List<DomainTerm> terms = ((DomainEq) indexGuard).getDomainTerms();
            for (int count = 0; count < terms.size(); count++) {
                if (terms.get(count) instanceof ArrayRead
                        || terms.get(count) instanceof DomainIte)
                    throw new InvalidIndexGuardException();

                if (terms.get(count).isEvar(uVars))
                    result.add(terms.get(count));

            }
            return result;
        }

        // something that is not an index guard.
        throw new InvalidIndexGuardException();
    }

    /**
     * Checks if the given formula is a valid index guard.
     * 
     * @param uVars
     *            the collection of universally quantified variables.
     * @param indexGuard
     *            the formula to check
     * @return <code>true</code> if the given <code>indexGuard</code> is a valid
     *         index guard, <code>false</code> otherwise.
     */
    private static boolean checkIndexGuard(Collection<DomainVariable> uVars,
            Formula indexGuard) {
        if (indexGuard instanceof PropositionalConstant)
            // only "true" is allowed in index guards
            return ((PropositionalConstant) indexGuard).getValue();

        if (indexGuard instanceof AndFormula) {
            for (Formula formula : ((AndFormula) indexGuard).getConjuncts())
                if (!ArrayProperty.checkIndexGuard(uVars, formula))
                    return false;
            return true;
        }

        if (indexGuard instanceof OrFormula) {

            for (Formula formula : ((OrFormula) indexGuard).getDisjuncts())
                if (!ArrayProperty.checkIndexGuard(uVars, formula))
                    return false;
            return true;
        }

        if (indexGuard instanceof DomainEq) {
            if (((DomainEq) indexGuard).isEqual())
                return true;
            else {
                List<DomainTerm> terms = ((DomainEq) indexGuard)
                        .getDomainTerms();
                for (int count = 0; count < terms.size(); count++) {
                    for (int inner_count = count + 1; inner_count < terms
                            .size(); inner_count++) {
                        if (terms.get(count) instanceof ArrayRead
                                || terms.get(count) instanceof DomainIte)
                            return false;
                        if (terms.get(inner_count) instanceof ArrayRead
                                || terms.get(inner_count) instanceof DomainIte)
                            return false;
                        if (!(terms.get(count).isEvar(uVars) || terms.get(
                                inner_count).isEvar(uVars)))
                            return false;
                    }
                }
                return true;
            }
        }

        // something that is not an index guard.
        return false;

    }

    /**
     * Returns a copy of the set of universally quantified variables.
     * 
     * @return the <code>uVars</code> (copy)
     */
    public Collection<DomainVariable> getuVars() {
        return new HashSet<DomainVariable>(uVars);
    }

    /**
     * Returns the index guard formula.
     * 
     * @return the <code>indexGuard</code>
     */
    public Formula getIndexGuard() {
        return indexGuard;
    }

    /**
     * Returns the value constraint formula.
     * 
     * @return the <code>valueConstraint</code>
     */
    public Formula getValueConstraint() {
        return valueConstraint;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental
        /*
         * List<DomainVariable> uVars = new ArrayList<DomainVariable>(); for
         * (DomainVariable uVar : this.uVars) uVars.add((DomainVariable)
         * uVar.deepTermCopy()); try { return new ArrayProperty(uVars,
         * indexGuard.deepFormulaCopy(), valueConstraint.deepFormulaCopy()); }
         * catch (InvalidIndexGuardException exc) { // This should never happen!
         * assert (false); throw new RuntimeException(
         * "Unexpected situation while copying array property.", exc);
         * 
         * } catch (InvalidValueConstraintException exc) { // This should never
         * happen! assert (false); throw new RuntimeException(
         * "Unexpected situation while copying array property.", exc); }
         */
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        valueConstraint.getArrayVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public void getDomainVariables(Set<DomainVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        valueConstraint.getDomainVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public void getPropositionalVariables(Set<PropositionalVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        indexGuard.getPropositionalVariables(result, done);
        valueConstraint.getPropositionalVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return ArrayProperty.create(new ArrayList<DomainVariable>(uVars),
                indexGuard.negationNormalForm(),
                valueConstraint.negationNormalForm());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        indexGuard.getUninterpretedFunctionNames(result, done);
        valueConstraint.getUninterpretedFunctionNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        indexGuard.getFunctionMacroNames(result, done);
        valueConstraint.getFunctionMacroNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
     */
    @Override
    public void getFunctionMacros(Set<FunctionMacro> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        indexGuard.getFunctionMacros(result, done);
        valueConstraint.getFunctionMacros(result, done);
        done.add(this);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof ArrayProperty))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        ArrayProperty other = (ArrayProperty) obj;
        return other.uVars.equals(uVars) && other.indexGuard.equals(indexGuard)
                && other.valueConstraint.equals(valueConstraint);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return uVars.hashCode() * 31 * 31 + indexGuard.hashCode() * 31
                + valueConstraint.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getId()
     */
    @Override
    public long getId() {
        return id;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        return ArrayProperty.getEVarsFromIndexGuard(uVars, indexGuard);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.containsKey(this)) {
            assert (done.get(this) != null);
            assert (done.get(this) instanceof Formula);
            return (Formula) done.get(this);
        }
        try {
            Formula result = ArrayProperty.create(uVars,
                    indexGuard.substituteFormula(paramMap, done),
                    valueConstraint.substituteFormula(paramMap, done));
            assert (result != null);
            done.put(this, result);
            return result;
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unable to convert ArrayProperty to caller scope.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualitiesTerm()
     */
    @Override
    public Formula removeArrayEqualities() {
        // Nothing to do.
        // ArrayProperties cannot contain array equalities.
        return this;
    }

    /**
     * Instantiates the body of this property by replacing the universally
     * quantified variables with the given terms.
     * 
     * @param indices
     *            the terms to use in place of the universally quantified
     *            variables.
     * @return an instance of this property's body with the given terms
     *         replacing universally quantified variables
     * @throws SuraqException
     *             if the number of indices does not match the number of
     *             <code>uVars</code>.
     */
    private Formula instantiate(List<DomainTerm> indices) throws SuraqException {
        if (indices.size() != uVars.size())
            throw new SuraqException(
                    "Wrong number of indices for instantiating array property");

        Map<Token, Term> substitutions = new HashMap<Token, Term>();
        for (int count = 0; count < uVars.size(); count++)
            substitutions.put(Token.generate(uVars.get(count).toString()),
                    indices.get(count));

        return ImpliesFormula.create(indexGuard.substituteFormula(
                substitutions, new HashMap<SMTLibObject, SMTLibObject>()),
                valueConstraint.substituteFormula(substitutions,
                        new HashMap<SMTLibObject, SMTLibObject>()));
    }

    /**
     * Returns a new formula that is the finite conjunction version of this
     * array property, instantiated over the given index set.
     * 
     * @param indexSet
     *            the index set.
     * @return the finite conjunction
     */
    public AndFormula toFiniteConjunction(Set<DomainTerm> indexSet) {
        assert (indexSet.size() > 0);
        List<Formula> conjuncts = new ArrayList<Formula>();
        List<DomainTerm> indices = new ArrayList<DomainTerm>(indexSet);
        List<Integer> counters = new ArrayList<Integer>();
        for (int count = 0; count < uVars.size(); count++)
            counters.add(0);
        do {
            List<DomainTerm> currentIndices = new ArrayList<DomainTerm>();
            for (int count = 0; count < counters.size(); count++)
                currentIndices.add(indices.get(counters.get(count)));
            try {
                conjuncts.add(this.instantiate(currentIndices));
            } catch (SuraqException exc) {
                throw new RuntimeException(
                        "Unexpected exception while converting array property to finite conjunction.",
                        exc);
            }

        } while (Util.incrementCounters(counters, indices.size()));
        return AndFormula.generate(conjuncts);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        throw new RuntimeException(
                "arrayPropertiesToFiniteConjunctions cannot be called on an ArrayProperty.\nUse toFiniteConjunction instead.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        // Not needed, as array properties are removed before simplifications.
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        try {
            return ArrayProperty.create(uVars, indexGuard.flatten(),
                    valueConstraint.flatten());
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unforseen exception while flattening array property.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return new SExpression(SExpressionConstants.FORALL, uVarsExpression(),
                (ImpliesFormula.create(indexGuard, valueConstraint))
                        .toSmtlibV2());
    }

    /**
     * Returns an s-expression of all universally quantified variables and their
     * type. E.g. ((var1 Value)(var2 Value)(var3 Value)).
     * 
     * @return s-expression of uvars.
     */
    private SExpression uVarsExpression() {
        List<SExpression> expr = new ArrayList<SExpression>();
        for (DomainVariable uVar : uVars)
            expr.add(new SExpression(uVar.toSmtlibV2(),
                    SExpressionConstants.VALUE_TYPE));
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        // Does not contain array writes subformulas.
        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        Formula indexGuard = this.indexGuard;
        Formula valueConstraint = this.valueConstraint;

        indexGuard = indexGuard
                .arrayReadsToUninterpretedFunctions(noDependenceVars);
        valueConstraint = valueConstraint
                .arrayReadsToUninterpretedFunctions(noDependenceVars);

        try {
            return ArrayProperty.create(uVars, indexGuard, valueConstraint);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        indexGuard.getUninterpretedFunctions(result, done);
        valueConstraint.getUninterpretedFunctions(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Formula substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions) {
        Formula indexGuard = this.indexGuard;
        Formula valueConstraint = this.valueConstraint;

        indexGuard = indexGuard.substituteUninterpretedFunction(substitutions);
        valueConstraint = valueConstraint
                .substituteUninterpretedFunction(substitutions);

        try {
            return ArrayProperty.create(uVars, indexGuard, valueConstraint);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.toSmtlibV2().toString();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(Formula,
     *      java.util.Set, Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Formula indexGuard = this.indexGuard;
        Formula valueConstraint = this.valueConstraint;

        indexGuard = indexGuard.makeArrayReadsSimple(topLevelFormula,
                constraints, noDependenceVars);
        valueConstraint = valueConstraint.makeArrayReadsSimple(topLevelFormula,
                constraints, noDependenceVars);

        try {
            return ArrayProperty.create(uVars, indexGuard, valueConstraint);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public Formula uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { try { return new ArrayProperty(uVars,
     * indexGuard.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars), valueConstraint
     * .uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars)); } catch (SuraqException exc) { throw new
     * RuntimeException( "Unexpectedly unable to create ArrayProperty.", exc); }
     * }
     */

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = this.indexGuard.getPartitionsFromSymbols();
        partitions.addAll(this.valueConstraint.getPartitionsFromSymbols());

        for (DomainVariable var : uVars)
            partitions.addAll(var.getPartitionsFromSymbols());

        return partitions;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */
    @Override
    public OrFormula transformToConsequentsForm() {
        throw new RuntimeException(
                "transformToConsequentsForm cannot be called on an ArrayProperty.\nArrays should be removed by now.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean,
     *      boolean)
     */
    @Override
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {
        throw new RuntimeException(
                "transformToConsequentsForm cannot be called on an ArrayProperty.\nArrays should be removed by now.");
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(SMTLibObject o) {
        return this.toString().compareTo(o.toString());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding,
            Map<Formula, PropositionalVariable> done, int partition) {
        throw new RuntimeException(
                "Array properties should have been removed before Tseitin encoding!");
    }

    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        throw new RuntimeException(
                "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an ArrayProperty.");

        /*
         * if (indexGuard instanceof UninterpretedPredicateInstance) indexGuard
         * = ((UninterpretedPredicateInstance)
         * indexGuard).applyReplaceUninterpretedPredicates(topLeveFormula,
         * predicateInstances, instanceParameters, noDependenceVars); else
         * indexGuard.uninterpretedPredicatesToAuxiliaryVariables(
         * topLeveFormula, predicateInstances, instanceParameters,
         * noDependenceVars);
         * 
         * if (valueConstraint instanceof UninterpretedPredicateInstance)
         * valueConstraint = ((UninterpretedPredicateInstance)
         * valueConstraint).applyReplaceUninterpretedPredicates(topLeveFormula,
         * predicateInstances, instanceParameters, noDependenceVars); else
         * valueConstraint.uninterpretedPredicatesToAuxiliaryVariables(
         * topLeveFormula, predicateInstances, instanceParameters,
         * noDependenceVars);
         */
    }

    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        throw new RuntimeException(
                "uninterpretedFunctionsToAuxiliaryVariables cannot be called on an ArrayProperty.");

        /*
         * indexGuard.uninterpretedFunctionsToAuxiliaryVariables(
         * topLeveFormula, functionInstances, instanceParameters,
         * noDependenceVars); valueConstraint
         * .uninterpretedFunctionsToAuxiliaryVariables( topLeveFormula,
         * functionInstances, instanceParameters, noDependenceVars);
         */

    }

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        throw new RuntimeException(
                "Arrays must be replaced on performing graph-based reduction to propositional logic.");
        /*
         * indexGuard = indexGuard.replaceEquivalences(topLeveFormula,
         * replacements); valueConstraint =
         * valueConstraint.replaceEquivalences(topLeveFormula, replacements);
         * return this;
         */
    }

    @Override
    public Formula removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        throw new RuntimeException(
                "Arrays must be replaced before removing DomainITE.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public Formula uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars) {
        try {
            return ArrayProperty.create(uVars, indexGuard
                    .uninterpretedFunctionsBackToArrayReads(arrayVars),
                    valueConstraint
                            .uninterpretedFunctionsBackToArrayReads(arrayVars));
        } catch (InvalidIndexGuardException exc) {
            throw new RuntimeException(
                    "Unexpected Excpetion while back-substituting array reads.",
                    exc);
        } catch (InvalidValueConstraintException exc) {
            throw new RuntimeException(
                    "Unexpected Excpetion while back-substituting array reads.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public Formula removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        Formula newIndexGuard = indexGuard.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        Formula newValueConstraint = valueConstraint.removeArrayITE(
                topLevelFormula, noDependenceVars, constraints);
        try {
            return ArrayProperty.create(uVars, newIndexGuard,
                    newValueConstraint);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unable to remove arrayITEs from array property.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeOut(java.io.BufferedWriter,
     *      at.iaik.suraq.util.HashTagContainer, boolean)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer,
            boolean handleThisWithTagContainer) throws IOException {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.write("(forall");
        for (DomainVariable var : uVars) {
            writer.write(" (");
            writer.write(var.getVarName());
            writer.write(" ");
            writer.write(SExpressionConstants.VALUE_TYPE.toString());
            writer.write(")");
        }
        writer.write(" (=> ");
        indexGuard.writeTo(writer);
        writer.write(" ");
        valueConstraint.writeTo(writer);
        writer.write(")");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeTo(java.io.Writer,
     *      java.util.Map)
     */
    @Override
    public void writeTo(Writer writer, Map<SMTLibObject, String> definitions)
            throws IOException {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getLiterals(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getLiterals(Set<Formula> result, Set<Formula> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#numAigNodes(java.util.Set)
     */
    @Override
    public int numAigNodes(Set<Formula> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toAig(TreeMap, java.util.Map)
     */
    @Override
    public int toAig(TreeMap<Integer, Integer[]> aigNodes,
            Map<Formula, Integer> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#size(boolean, java.util.Map)
     */
    @Override
    public long size(boolean expandDAG, Map<Formula, Long> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#computeParents(java.util.Map,
     *      java.util.Set)
     */
    @Override
    public void computeParents(Map<Formula, Set<Formula>> parents,
            Set<Formula> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#computeSubformulasWithOnlyLeafChildren(java.util.Set,
     *      java.util.HashSet)
     */
    @Override
    public void computeSubformulasWithOnlyLeafChildren(
            Set<Formula> onlyLeafChildren, Set<Formula> leaves,
            Set<Formula> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getTerms(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getTerms(Set<Term> result, Set<Formula> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#dependsOnlyOn(java.util.Set)
     */
    @Override
    public boolean dependsOnlyOn(Set<Formula> formulaSet) {
        throw new NotImplementedException();
    }

}
