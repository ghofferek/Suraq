/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Writer;
import java.lang.reflect.Constructor;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.HashTagContainer;
import at.iaik.suraq.util.ImmutableArrayList;

/**
 * A common superclass for And- Or- and Xor-formulas to avoid code redundancy.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class AndOrXorFormula extends BooleanCombinationFormula {
    /**
     * 
     */
    private static final long serialVersionUID = 3515032983832421411L;
    /**
     * The list of sub-formulas.
     */
    protected final ImmutableArrayList<Formula> formulas;

    private final int hashCode;

    /**
     * 
     * Constructs a new <code>AndOrXorFormula</code>. Initializes the list of
     * subformulas.
     * 
     * @param formulas
     *            the list of subformulas.
     */
    protected AndOrXorFormula(List<? extends Formula> formulas) {
        ArrayList<Formula> tmp = new ArrayList<Formula>();
        for (Formula formula : formulas) {
            if (formula instanceof FormulaTerm)
                tmp.add(((FormulaTerm) formula).getFormula());
            else
                tmp.add(formula);
        }
        if (formulas.size() < 1)
            tmp.add(PropositionalConstant.create(true));

        this.formulas = new ImmutableArrayList<Formula>(tmp);
        this.hashCode = formulas.hashCode();
    }

    /**
     * Creates a new <code>AndOrXorFormula</code> which is of the same type as
     * <code>this</code> object and has the given subformulas.
     * 
     * @param formulas
     *            the subformulas
     * @return a new <code>AndOrXorFormula</code> with the same type as
     *         <code>this</code>.
     */
    protected AndOrXorFormula create(List<? extends Formula> formulas) {
        Class<? extends AndOrXorFormula> myClass = this.getClass();
        // Class<?> listClass = formulas.getClass();
        AndOrXorFormula instance = null;
        try {
            Constructor<?>[] constructors = myClass.getDeclaredConstructors();
            if (constructors.length == 0)
                throw new RuntimeException("No constructors found.");
            for (Constructor<?> constructor : constructors) {
                Class<?>[] parameters = constructor.getParameterTypes();
                if (parameters.length != 1)
                    continue;
                if (!(parameters[0].isInstance(formulas)))
                    continue;
                instance = (AndOrXorFormula) constructor.newInstance(formulas);
            }
            if (instance == null)
                throw new RuntimeException();

            return FormulaCache.andOrXorFormula.put(instance);
            // return instance;
        } catch (Throwable exc) {
            exc.printStackTrace();
            throw new RuntimeException("Unable to create AndOrXorFormula", exc);
        }
        // TODO: cache!!!
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Formula formula : formulas)
            formula.getArrayVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getDomainVariables()
     */
    @Override
    public void getDomainVariables(Set<DomainVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Formula formula : formulas)
            formula.getDomainVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getPropositionalVariables()
     */
    @Override
    public void getPropositionalVariables(Set<PropositionalVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Formula formula : formulas)
            formula.getPropositionalVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        return new ArrayList<Formula>(formulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental

        /*
         * List<Formula> subformulas = new ArrayList<Formula>(); for (Formula
         * formula : formulas) { if (formula == null)
         * System.out.println(formula);
         * 
         * subformulas.add(formula.deepFormulaCopy()); } return
         * create(subformulas);
         */
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        List<Formula> nnfFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            nnfFormulas.add(formula.negationNormalForm());

        return create(nnfFormulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Formula formula : formulas)
            formula.getUninterpretedFunctionNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Formula formula : formulas)
            formula.getFunctionMacroNames(result, done);
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
        for (Formula formula : formulas)
            formula.getFunctionMacros(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> indexSet = new HashSet<DomainTerm>();
        for (Formula formula : formulas)
            indexSet.addAll(formula.getIndexSet());
        return indexSet;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;

        if (obj == null)
            return false;

        if (this.hashCode() != obj.hashCode())
            return false;

        if (!(this.getClass().isInstance(obj)))
            return false;

        return this.formulas.equals(((AndOrXorFormula) obj).formulas);

    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        /*
         * int hashCode = 0; for (Formula formula : formulas) hashCode ^=
         * formula.hashCode();
         */
        return this.hashCode;
        // NOTE, that the hashcode will be the same for an AND and an OR-Class
        // with the same attributes
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
        List<Formula> convertedFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            convertedFormulas.add(formula.substituteFormula(paramMap, done));

        Formula result = create(convertedFormulas);
        assert (result != null);
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualitiesTerm()
     */
    @Override
    public Formula removeArrayEqualities() {
        List<Formula> children = new ArrayList<Formula>();

        for (int count = 0; count < formulas.size(); count++) {
            if (formulas.get(count) instanceof ArrayEq)
                children.add(((ArrayEq) formulas.get(count))
                        .toArrayProperties());
            else
                children.add(formulas.get(count).removeArrayEqualities());
        }
        return create(children);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        List<Formula> children = new ArrayList<Formula>();

        for (int count = 0; count < formulas.size(); count++) {
            if (formulas.get(count) instanceof ArrayProperty)
                children.add(((ArrayProperty) formulas.get(count))
                        .toFiniteConjunction(indexSet));
            else
                children.add(formulas.get(count)
                        .arrayPropertiesToFiniteConjunctions(indexSet));
        }
        return create(children);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        List<Formula> children = new ArrayList<Formula>();
        // Default, unless a subclass has more clever method
        for (int count = 0; count < formulas.size(); count++)
            children.add(formulas.get(count).simplify());
        return create(children);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        List<Formula> flattenedFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            flattenedFormulas.add(formula.flatten());

        return create(flattenedFormulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> children = new ArrayList<SExpression>();
        children.add(this.getOperator());
        for (Formula formula : formulas)
            children.add(formula.toSmtlibV2());
        return new SExpression(children);
    }

    /**
     * Returns the token representing the operator (and/or/xor) of this formula.
     * 
     * @return The operator token.
     */
    protected abstract Token getOperator();

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        List<Formula> children = new ArrayList<Formula>();
        for (Formula formula : this.getSubFormulas())
            children.add(formula.removeArrayWrites(topLevelFormula,
                    constraints, noDependenceVars));
        return create(children);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        List<Formula> children = new ArrayList<Formula>();
        for (Formula formula : formulas)
            children.add(formula
                    .arrayReadsToUninterpretedFunctions(noDependenceVars));
        return create(children);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Formula formula : formulas)
            formula.getUninterpretedFunctions(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Formula substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null) {
            assert (done.get(this) instanceof Formula);
            return (Formula) done.get(this);
        }
        List<Formula> children = new ArrayList<Formula>();
        for (Formula formula : formulas)
            children.add(formula.substituteUninterpretedFunction(substitutions,
                    done));

        Formula result = create(children);
        done.put(this, result);
        return result;
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
        List<Formula> children = new ArrayList<Formula>();
        for (Formula formula : formulas)
            children.add(formula.makeArrayReadsSimple(topLevelFormula,
                    constraints, noDependenceVars));
        return create(children);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public Formula uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { List<Formula> newFormulas = new ArrayList<Formula>();
     * for (Formula formula : formulas) newFormulas.add(formula
     * .uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars));
     * 
     * return this.create(newFormulas); }
     */

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = new TreeSet<Integer>();

        for (Formula formula : formulas)
            partitions.addAll(formula.getPartitionsFromSymbols());
        return partitions;
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

        List<Formula> children = new ArrayList<Formula>();

        Collection<Formula> subformulas = this.getSubFormulas();

        for (Formula formula : subformulas)
            if (formula instanceof UninterpretedPredicateInstance) {

                Formula auxVar = ((UninterpretedPredicateInstance) formula)
                        .applyReplaceUninterpretedPredicates(topLeveFormula,
                                predicateInstances, instanceParameters,
                                noDependenceVars);

                // added by chille: 03.07.2012
                children.add(auxVar);

                // removed by chille:
                // formulas.remove(formula);
                // formulas.add(auxVar);
            } else
                children.add(formula
                        .uninterpretedPredicatesToAuxiliaryVariables(
                                topLeveFormula, predicateInstances,
                                instanceParameters, noDependenceVars));
        return create(children);

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
        List<Formula> children = new ArrayList<Formula>();
        for (Formula formula : this.getSubFormulas())
            children.add(formula.uninterpretedFunctionsToAuxiliaryVariables(
                    topLeveFormula, functionInstances, instanceParameters,
                    noDependenceVars));
        return create(children);
    }

    @Override
    public Formula replaceEquivalences(Formula topLevelFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        List<Formula> children = new ArrayList<Formula>();
        for (int i = 0; i < formulas.size(); i++)
            children.add(formulas.get(i).replaceEquivalences(topLevelFormula,
                    replacements, noDependenceVars));
        return create(children);
    }

    @Override
    public Formula removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        List<Formula> children = new ArrayList<Formula>();
        for (int i = 0; i < formulas.size(); i++)

            children.add(formulas.get(i).removeDomainITE(topLevelFormula,
                    noDependenceVars, andPreList));
        return create(children);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public Formula uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars) {
        List<Formula> newFormulas = new ArrayList<Formula>(formulas.size());
        for (Formula formula : formulas) {
            Formula newFormula = formula
                    .uninterpretedFunctionsBackToArrayReads(arrayVars);
            newFormulas.add(newFormula);
        }
        return this.create(newFormulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public AndOrXorFormula removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        List<Formula> newSubformulas = new ArrayList<Formula>(formulas.size());
        for (Formula subformula : formulas) {
            newSubformulas.add(subformula.removeArrayITE(topLevelFormula,
                    noDependenceVars, constraints));
        }
        return this.create(newSubformulas);
    }

    /**
     * @throws IOException
     * @see at.iaik.suraq.smtlib.formula.Formula#writeOut(java.io.BufferedWriter,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer,
            boolean handleThisWithTagContainer) throws IOException {

        if (handleThisWithTagContainer)
            tagContainer.handle(this, writer);
        else {

            writer.append('(');
            if (this instanceof AndFormula)
                writer.append(SExpressionConstants.AND.toString());
            else {
                if (this instanceof OrFormula)
                    writer.append(SExpressionConstants.OR.toString());
                else {
                    if (this instanceof XorFormula)
                        writer.append(SExpressionConstants.XOR.toString());
                    else {
                        throw new RuntimeException("Unexpected formula type.");
                    }
                }
            }
            writer.append(' ');
            for (Formula subformula : formulas) {
                subformula.writeOut(writer, tagContainer, true);
            }
            writer.append(") ");
        }

    }

    /**
     * @throws IOException
     * @see at.iaik.suraq.smtlib.formula.Formula#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.append('(');
        if (this instanceof AndFormula)
            writer.append(SExpressionConstants.AND.toString());
        else {
            if (this instanceof OrFormula)
                writer.append(SExpressionConstants.OR.toString());
            else {
                if (this instanceof XorFormula)
                    writer.append(SExpressionConstants.XOR.toString());
                else {
                    throw new RuntimeException("Unexpected formula type.");
                }
            }
        }
        for (Formula subformula : formulas) {
            writer.append(' ');
            subformula.writeTo(writer);
        }
        writer.append(") ");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeTo(java.io.Writer,
     *      java.util.Map)
     */
    @Override
    public void writeTo(Writer writer, Map<SMTLibObject, String> definitions)
            throws IOException {
        writer.append('(');
        if (this instanceof AndFormula)
            writer.append(SExpressionConstants.AND.toString());
        else {
            if (this instanceof OrFormula)
                writer.append(SExpressionConstants.OR.toString());
            else {
                if (this instanceof XorFormula)
                    writer.append(SExpressionConstants.XOR.toString());
                else {
                    throw new RuntimeException("Unexpected formula type.");
                }
            }
        }
        for (Formula subformula : formulas) {
            writer.append(' ');
            String id = definitions.get(subformula);
            assert (id != null);
            writer.append(id);
        }
        writer.append(") ");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getLiterals(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getLiterals(Set<Formula> result, Set<Formula> done) {
        if (done.contains(this))
            return;
        for (Formula subformula : formulas)
            subformula.getLiterals(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#size(boolean, java.util.Map)
     */
    @Override
    public BigInteger size(boolean expandDAG, Map<Formula, BigInteger> done) {
        if (done.get(this) != null) {
            if (expandDAG)
                return done.get(this);
            else
                return BigInteger.ZERO;
        }

        BigInteger result = BigInteger.ONE;
        for (Formula formula : formulas)
            result = result.add(formula.size(expandDAG, done));

        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#computeParents(java.util.Map,
     *      java.util.Set)
     */
    @Override
    public void computeParents(Map<Formula, Set<Formula>> parents,
            Set<Formula> done) {
        if (done.contains(this))
            return;

        for (Formula child : formulas) {
            Set<Formula> childsParents = parents.get(child);
            if (childsParents == null) {
                childsParents = new TreeSet<Formula>();
                parents.put(child, childsParents);
            }
            assert (childsParents != null);
            childsParents.add(this);
            child.computeParents(parents, done);
        }

        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#computeSubformulasWithOnlyLeafChildren(java.util.Set,
     *      java.util.HashSet)
     */
    @Override
    public void computeSubformulasWithOnlyLeafChildren(
            Set<Formula> onlyLeafChildren, Set<Formula> leaves,
            Set<Formula> done) {
        if (done.contains(this))
            return;
        if (leaves.contains(this)) {
            done.add(this);
            return;
        }

        boolean result = true;
        for (Formula formula : formulas) {
            if (!leaves.contains(formula))
                result = false;
            formula.computeSubformulasWithOnlyLeafChildren(onlyLeafChildren,
                    leaves, done);
        }
        if (result)
            onlyLeafChildren.add(this);

        done.add(this);
        return;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getTerms(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getTerms(Set<Term> result, Set<Formula> done) {
        if (done.contains(this))
            return;

        for (Formula formula : formulas)
            formula.getTerms(result, done);

        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#dependsOnlyOn(java.util.Set)
     */
    @Override
    public boolean dependsOnlyOn(Set<Formula> formulaSet) {
        if (formulaSet.containsAll(formulas))
            return true;
        return false;
    }

}
