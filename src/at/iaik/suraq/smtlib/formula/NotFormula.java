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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.HashTagContainer;
import at.iaik.suraq.util.Util;

/**
 * A formula representing the negation of another one.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class NotFormula extends BooleanCombinationFormula {

    /**
     * 
     */
    private static final long serialVersionUID = -99679765405836941L;
    /**
     * The negated internal formula.
     */
    private final Formula formula;

    private final int hashCode;

    public static NotFormula create(Formula formula) {
        return FormulaCache.notFormula.put(new NotFormula(formula));
    }

    /**
     * 
     * Constructs a new <code>NotFormula</code>.
     * 
     * @param formula
     *            the negation of this formula.
     */
    private NotFormula(Formula formula) {
        if (formula instanceof FormulaTerm)
            this.formula = ((FormulaTerm) formula).getFormula();
        else
            this.formula = formula;
        hashCode = formula.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        List<Formula> list = new ArrayList<Formula>();
        list.add(formula);
        return list;
    }

    /**
     * Returns a copy of the negated formula.
     * 
     * @return A copy of the negated formula.
     */
    public Formula getNegatedFormula() {
        return formula.deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental
        // return NotFormula.create(formula.deepFormulaCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
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
        formula.getPropositionalVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {

        // And
        if (formula instanceof AndFormula) {
            List<Formula> subformulas = new ArrayList<Formula>();
            for (Formula subformula : ((AndOrXorFormula) formula).formulas)
                subformulas.add((NotFormula.create(subformula))
                        .negationNormalForm());
            return OrFormula.generate(subformulas);
        }

        // Or
        if (formula instanceof OrFormula) {
            List<Formula> subformulas = new ArrayList<Formula>();
            for (Formula subformula : ((AndOrXorFormula) formula).formulas)
                subformulas.add((NotFormula.create(subformula))
                        .negationNormalForm());
            return AndFormula.generate(subformulas);
        }

        // Xor
        if (formula instanceof XorFormula) {
            Formula converted = ((XorFormula) formula).toAndOrFormula();
            return (NotFormula.create(converted)).negationNormalForm();
        }

        // Not
        if (formula instanceof NotFormula) {
            return ((NotFormula) formula).formula.negationNormalForm();
        }

        // Equality
        if (formula instanceof EqualityFormula) {
            EqualityFormula eqFormula = (EqualityFormula) formula;
            if (eqFormula.isPair())
                return EqualityFormula.create(eqFormula.getTerms(),
                        !eqFormula.isEqual());

            AndFormula pairwise = eqFormula.toPairwise();
            return (NotFormula.create(pairwise)).negationNormalForm();
        }

        // ArrayProperty
        if (formula instanceof ArrayProperty) {
            throw new UnsupportedOperationException(
                    "NNF of array properties not implemented!");
        }

        // PropositionalConstant
        if (formula instanceof PropositionalConstant)
            return PropositionalConstant
                    .create(!((PropositionalConstant) formula).getValue());

        // PropositionalVariable
        if (formula instanceof PropositionalVariable)
            return this.deepFormulaCopy();

        // Implies
        if (formula instanceof ImpliesFormula) {
            ImpliesFormula impliesFormula = (ImpliesFormula) formula;
            List<Formula> list = new ArrayList<Formula>();
            list.add(impliesFormula.getLeftSide().negationNormalForm());
            list.add((NotFormula.create(impliesFormula.getRightSide()))
                    .negationNormalForm());
            return AndFormula.generate(list);
        }

        // MacroInstance
        if (formula instanceof PropositionalFunctionMacroInstance) {
            PropositionalFunctionMacro negatedMacro = ((PropositionalFunctionMacroInstance) formula)
                    .getMacro().negatedMacro();
            Map<Token, Term> paramMap = new HashMap<Token, Term>(
                    ((PropositionalFunctionMacroInstance) formula)
                            .getParamMap());
            return PropositionalFunctionMacroInstance.create(negatedMacro,
                    paramMap);
        }

        // PropositionalITE
        if (formula instanceof PropositionalIte) {
            PropositionalIte iteFormula = (PropositionalIte) formula;
            Formula thenBranch = (NotFormula.create(iteFormula.getThenBranch()))
                    .negationNormalForm();
            Formula elseBranch = (NotFormula.create(iteFormula.getElseBranch()))
                    .negationNormalForm();
            return PropositionalIte.create(iteFormula.getCondition()
                    .negationNormalForm(), thenBranch, elseBranch);
        }

        // something unexpected
        throw new SuraqException(
                "Unexpected formula type while trying to convert to NNF:"
                        + formula.getClass().toString());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
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
        formula.getFunctionMacros(result, done);
        done.add(this);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof NotFormula))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        return ((NotFormula) obj).formula.equals(formula);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        return formula.getIndexSet();
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
        Formula result = NotFormula.create(formula.substituteFormula(paramMap,
                done));
        assert (result != null);
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualitiesTerm()
     */
    @Override
    public Formula removeArrayEqualities() {
        Formula formula = this.formula;
        if (formula instanceof ArrayEq)
            formula = ((ArrayEq) formula).toArrayProperties();
        else
            formula = formula.removeArrayEqualities();
        return NotFormula.create(formula);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        Formula formula = this.formula;
        if (formula instanceof ArrayProperty)
            formula = ((ArrayProperty) formula).toFiniteConjunction(indexSet);
        else
            formula = formula.arrayPropertiesToFiniteConjunctions(indexSet);
        return NotFormula.create(formula);
    }

    /**
     * Checks whether this <code>NotFormula</code> is a negated propositional
     * variable. If so, the variable is returned (without the negation).
     * 
     * @return If this <code>NotFormula</code> is the negation of a
     *         <code>PropositionalVariable</code>, the variable is returned.
     *         Else, <code>null</code> is returned.
     */
    public PropositionalVariable isNegatedVariable() {
        if (!(formula instanceof PropositionalVariable))
            return null;
        else
            return (PropositionalVariable) formula;
    }

    /**
     * Checks whether this <code>NotFormula</code> is a negated propositional
     * constant. If so, the constant is returned (without the negation).
     * 
     * @return If this <code>NotFormula</code> is the negation of a
     *         <code>PropositionalConstant</code>, it is returned. Else,
     *         <code>null</code> is returned.
     */
    public PropositionalConstant isNegatedConstant() {
        if (!(formula instanceof PropositionalConstant))
            return null;
        else
            return (PropositionalConstant) formula;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        Formula formula = this.formula.simplify();

        if (formula instanceof PropositionalConstant)
            return PropositionalConstant
                    .create(!((PropositionalConstant) formula).getValue());

        if (formula instanceof NotFormula)
            return ((NotFormula) formula).formula;

        return NotFormula.create(formula);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        return NotFormula.create(formula.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return new SExpression(SExpressionConstants.NOT, formula.toSmtlibV2());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return NotFormula.create(formula.removeArrayWrites(topLevelFormula,
                constraints, noDependenceVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        return NotFormula.create(formula
                .arrayReadsToUninterpretedFunctions(noDependenceVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
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
        Formula result = NotFormula.create(formula
                .substituteUninterpretedFunction(substitutions, done));
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        return NotFormula.create(formula.makeArrayReadsSimple(topLevelFormula,
                constraints, noDependenceVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public Formula uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { return NotFormula.create(
     * formula.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars)); }
     */

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {

        return formula.getPartitionsFromSymbols();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */
    @Override
    public OrFormula transformToConsequentsForm() {
        return (OrFormula) transformToConsequentsForm(false, true);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean,
     *      boolean)
     */
    @Override
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {

        Formula notFormula;

        if (isValidChild(this.formula)) {

            notFormula = this.formula.transformToConsequentsForm(!notFlag,
                    false);

            if (firstLevel == true) {
                if (Util.isLiteral(notFormula)) {
                    List<Formula> literals = new ArrayList<Formula>();
                    literals.add(notFormula);
                    Formula orFormula = OrFormula.generate(literals);
                    return orFormula;
                } else if (notFormula instanceof OrFormula) {
                    return notFormula;
                } else
                    throw new RuntimeException(
                            "Clausel should always be a Or Formula");
            }

            return notFormula;

        } else
            throw new RuntimeException("Not formula has no valid child.");
    }

    /**
     * Checks if a given formula is a valid child for a NOT Formula.
     * 
     * @param formula
     *            formula to check
     * @return true, iff formula is valid
     */
    public boolean isValidChild(Formula formula) {
        if (formula instanceof OrFormula)
            return true;
        if (formula instanceof AndFormula)
            return true;
        if (formula instanceof NotFormula)
            return true;
        if (formula instanceof ImpliesFormula)
            return true;
        if (Util.isLiteral(formula))
            return true;
        return false;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding,
            Map<Formula, PropositionalVariable> done, int partition) {

        assert (clauses != null);
        assert (encoding != null);
        assert (done != null);
        if (done.get(this) != null)
            return done.get(this);

        Set<Integer> partitions = this.getPartitionsFromSymbols();
        assert (partitions.size() == 1 || partitions.size() == 2);
        if (partitions.size() == 2)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        assert (partitions.iterator().next().equals(partition) || partitions
                .iterator().next().equals(-1));

        PropositionalVariable tseitinVar = Util.freshTseitinVar(partition);
        encoding.put(tseitinVar, this);
        done.put(this, tseitinVar);

        Formula tseitinVarForSubformula = formula.tseitinEncode(clauses,
                encoding, done, partition);
        assert (Util.isLiteral(tseitinVarForSubformula));

        List<Formula> disjuncts = new ArrayList<Formula>(2);
        disjuncts.add(tseitinVar);
        disjuncts.add(tseitinVarForSubformula);
        clauses.add(OrFormula.generate(disjuncts));

        disjuncts.clear();
        disjuncts.add(NotFormula.create(tseitinVar));
        disjuncts.add(NotFormula.create(tseitinVarForSubformula));
        clauses.add(OrFormula.generate(disjuncts));

        return tseitinVar;
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
        Formula formula = this.formula;
        if (formula instanceof UninterpretedPredicateInstance)
            formula = ((UninterpretedPredicateInstance) formula)
                    .applyReplaceUninterpretedPredicates(topLeveFormula,
                            predicateInstances, instanceParameters,
                            noDependenceVars);
        else
            formula = formula.uninterpretedPredicatesToAuxiliaryVariables(
                    topLeveFormula, predicateInstances, instanceParameters,
                    noDependenceVars);
        return NotFormula.create(formula);
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
        return NotFormula
                .create(formula.uninterpretedFunctionsToAuxiliaryVariables(
                        topLeveFormula, functionInstances, instanceParameters,
                        noDependenceVars));
    }

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        return NotFormula.create(formula.replaceEquivalences(topLeveFormula,
                replacements, noDependenceVars));
    }

    @Override
    public Formula removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        return NotFormula.create(formula.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public Formula uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars) {
        return NotFormula.create(formula
                .uninterpretedFunctionsBackToArrayReads(arrayVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public Formula removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        return NotFormula.create(formula.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeOut(java.io.BufferedWriter,
     *      at.iaik.suraq.util.HashTagContainer, boolean)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer,
            boolean handleThisWithTagContainer) throws IOException {
        if (handleThisWithTagContainer) {
            tagContainer.handle(this, writer);
        } else {
            writer.append('(').append(SExpressionConstants.NOT.toString());
            writer.append(' ');
            formula.writeOut(writer, tagContainer, true);
            writer.append(')');
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.append('(').append(SExpressionConstants.NOT.toString());
        writer.append(' ');
        formula.writeTo(writer);
        writer.append(')');

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeTo(java.io.Writer,
     *      java.util.Map)
     */
    @Override
    public void writeTo(Writer writer, Map<SMTLibObject, String> definitions)
            throws IOException {
        writer.append('(').append(SExpressionConstants.NOT.toString());
        writer.append(' ');
        String id = definitions.get(formula);
        assert (id != null);
        writer.write(id);
        writer.append(')');
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getLiterals(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getLiterals(Set<Formula> result, Set<Formula> done) {
        if (done.contains(this))
            return;
        formula.getLiterals(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#numAigNodes(java.util.Set)
     */
    @Override
    public int numAigNodes(Set<Formula> done) {
        if (done.contains(this))
            return 0;
        int result = formula.numAigNodes(done);
        done.add(this);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toAig(TreeMap, java.util.Map)
     */
    @Override
    public int toAig(TreeMap<Integer, Integer[]> aigNodes,
            Map<Formula, Integer> done) {
        if (done.get(this) != null)
            return done.get(this);

        int result = formula.toAig(aigNodes, done);
        result ^= 1;
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#size(boolean, java.util.Map)
     */
    @Override
    public long size(boolean expandDAG, Map<Formula, Long> done) {
        if (done.get(this) != null) {
            if (expandDAG)
                return done.get(this);
            else
                return 0;
        }

        long result = 1;
        result += formula.size(expandDAG, done);

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
        Set<Formula> childsParents = parents.get(formula);
        if (childsParents == null) {
            childsParents = new TreeSet<Formula>();
            parents.put(formula, childsParents);
        }
        assert (childsParents != null);
        childsParents.add(this);
        formula.computeParents(parents, done);

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
        if (!leaves.contains(formula))
            result = false;
        formula.computeSubformulasWithOnlyLeafChildren(onlyLeafChildren,
                leaves, done);
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

        formula.getTerms(result, done);

        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#dependsOnlyOn(java.util.Set)
     */
    @Override
    public boolean dependsOnlyOn(Set<Formula> formulaSet) {
        return formula.dependsOnlyOn(formulaSet);
    }

}
