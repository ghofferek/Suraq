/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
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
 * A class for formulas of the form (a => b).
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ImpliesFormula extends BooleanCombinationFormula {

    /**
     * 
     */
    private static final long serialVersionUID = -701197449376211245L;

    /**
     * The left side of the implication.
     */
    private final Formula leftSide;

    /**
     * The right side of the implication.
     */
    private final Formula rightSide;

    public static ImpliesFormula create(Formula leftSide, Formula rightSide) {
        return FormulaCache.impliesFormula.put(new ImpliesFormula(leftSide,
                rightSide));
    }

    /**
     * 
     * Constructs a new <code>ImpliesFormula</code>.
     * 
     * @param leftSide
     *            the left side of the implication
     * @param rightSide
     *            the right side of the implication
     */
    private ImpliesFormula(Formula leftSide, Formula rightSide) {
        if (leftSide instanceof FormulaTerm)
            this.leftSide = ((FormulaTerm) leftSide).getFormula();
        else
            this.leftSide = leftSide;

        if (rightSide instanceof FormulaTerm)
            this.rightSide = ((FormulaTerm) rightSide).getFormula();
        else
            this.rightSide = rightSide;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        List<Formula> list = new ArrayList<Formula>();
        list.add(leftSide);
        list.add(rightSide);
        return list;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental
        // return new ImpliesFormula(leftSide.deepFormulaCopy(),
        // rightSide.deepFormulaCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        leftSide.getArrayVariables(result, done);
        rightSide.getArrayVariables(result, done);
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
        leftSide.getDomainVariables(result, done);
        rightSide.getDomainVariables(result, done);
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
        leftSide.getPropositionalVariables(result, done);
        rightSide.getPropositionalVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        List<Formula> list = new ArrayList<Formula>();
        list.add((NotFormula.create(leftSide)).negationNormalForm());
        list.add(rightSide.negationNormalForm());
        return OrFormula.generate(list);
    }

    /**
     * @return the <code>leftSide</code>
     */
    public Formula getLeftSide() {
        return leftSide;
    }

    /**
     * @return the <code>rightSide</code>
     */
    public Formula getRightSide() {
        return rightSide;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        leftSide.getUninterpretedFunctionNames(result, done);
        rightSide.getUninterpretedFunctionNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        leftSide.getFunctionMacroNames(result, done);
        rightSide.getFunctionMacroNames(result, done);
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
        leftSide.getFunctionMacros(result, done);
        rightSide.getFunctionMacros(result, done);
        done.add(this);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof ImpliesFormula))
            return false;

        if (this.hashCode() != obj.hashCode())
            return false;
        return ((ImpliesFormula) obj).leftSide.equals(leftSide)
                && ((ImpliesFormula) obj).rightSide.equals(rightSide);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return leftSide.hashCode() * 31 + rightSide.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = leftSide.getIndexSet();
        result.addAll(rightSide.getIndexSet());
        return result;
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
        Formula result = ImpliesFormula.create(
                leftSide.substituteFormula(paramMap, done),
                rightSide.substituteFormula(paramMap, done));
        assert (result != null);
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualitiesTerm()
     */
    @Override
    public Formula removeArrayEqualities() {
        Formula rightSide = this.rightSide;
        Formula leftSide = this.leftSide;
        if (leftSide instanceof ArrayEq)
            leftSide = ((ArrayEq) leftSide).toArrayProperties();
        else
            leftSide = leftSide.removeArrayEqualities();

        if (rightSide instanceof ArrayEq)
            rightSide = ((ArrayEq) rightSide).toArrayProperties();
        else
            rightSide = rightSide.removeArrayEqualities();

        return ImpliesFormula.create(leftSide, rightSide);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        Formula rightSide = this.rightSide;
        Formula leftSide = this.leftSide;
        if (leftSide instanceof ArrayProperty)
            leftSide = ((ArrayProperty) leftSide).toFiniteConjunction(indexSet);
        else
            leftSide = leftSide.arrayPropertiesToFiniteConjunctions(indexSet);

        if (rightSide instanceof ArrayProperty)
            rightSide = ((ArrayProperty) rightSide)
                    .toFiniteConjunction(indexSet);
        else
            rightSide = rightSide.arrayPropertiesToFiniteConjunctions(indexSet);
        return ImpliesFormula.create(leftSide, rightSide);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        Formula leftSide = this.leftSide.simplify();
        Formula rightSide = this.rightSide.simplify();

        if (leftSide instanceof PropositionalConstant) {
            if (((PropositionalConstant) leftSide).getValue())
                return rightSide;
            else
                return PropositionalConstant.create(true);
        }

        if (rightSide instanceof PropositionalConstant) {
            if (((PropositionalConstant) rightSide).getValue())
                return PropositionalConstant.create(true);
            else
                return NotFormula.create(leftSide).simplify();
        }

        if (leftSide.equals(rightSide))
            return PropositionalConstant.create(true);

        if (leftSide instanceof NotFormula)
            if (rightSide.equals(((NotFormula) leftSide).getNegatedFormula()))
                return rightSide;

        if (rightSide instanceof NotFormula)
            if (leftSide.equals(((NotFormula) rightSide).getNegatedFormula()))
                return rightSide;

        return ImpliesFormula.create(leftSide, rightSide);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        return ImpliesFormula.create(leftSide.flatten(), rightSide.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        return new SExpression(SExpressionConstants.IMPLIES,
                leftSide.toSmtlibV2(), rightSide.toSmtlibV2());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Formula rightSide = this.rightSide;
        Formula leftSide = this.leftSide;
        leftSide = leftSide.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
        rightSide = rightSide.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
        return ImpliesFormula.create(leftSide, rightSide);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        Formula rightSide = this.rightSide;
        Formula leftSide = this.leftSide;
        leftSide = leftSide
                .arrayReadsToUninterpretedFunctions(noDependenceVars);
        rightSide = rightSide
                .arrayReadsToUninterpretedFunctions(noDependenceVars);
        return ImpliesFormula.create(leftSide, rightSide);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        leftSide.getUninterpretedFunctions(result, done);
        rightSide.getUninterpretedFunctions(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Formula substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions) {
        Formula rightSide = this.rightSide;
        Formula leftSide = this.leftSide;
        leftSide = leftSide.substituteUninterpretedFunction(substitutions);
        rightSide = rightSide.substituteUninterpretedFunction(substitutions);
        return ImpliesFormula.create(leftSide, rightSide);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Formula rightSide = this.rightSide;
        Formula leftSide = this.leftSide;
        leftSide = leftSide.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        rightSide = rightSide.makeArrayReadsSimple(topLevelFormula,
                constraints, noDependenceVars);
        return ImpliesFormula.create(leftSide, rightSide);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public Formula uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { return new ImpliesFormula(
     * leftSide.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars),
     * rightSide.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars)); }
     */

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = this.leftSide.getPartitionsFromSymbols();
        partitions.addAll(this.rightSide.getPartitionsFromSymbols());

        return partitions;
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

        // a => b equals NOT a OR b

        if (notFlag == true)
            throw new RuntimeException(
                    "An implies formula is now allowed to occur inside an NOT formula");

        List<Formula> subFormulas = new ArrayList<Formula>();

        if (isValidChild(this.leftSide)) {
            if (this.leftSide instanceof AndFormula) {

                ArrayList<Formula> conjuncts = (ArrayList<Formula>) ((AndFormula) this.leftSide)
                        .getConjuncts();
                for (Formula conjunct : conjuncts) {

                    // remove nested AND formula
                    if (conjunct instanceof AndFormula) {
                        ArrayList<Formula> subConjuncts = (ArrayList<Formula>) ((AndFormula) conjunct)
                                .getConjuncts();
                        for (Formula subConjunct : subConjuncts) {
                            Formula transformedSubFormula = subConjunct
                                    .transformToConsequentsForm(!notFlag, false);
                            subFormulas.add(transformedSubFormula);
                        }

                    } else {
                        Formula transformedSubFormula = conjunct
                                .transformToConsequentsForm(!notFlag, false);
                        subFormulas.add(transformedSubFormula);
                    }
                }
            } else if (Util.isLiteral(this.leftSide)
                    || this.leftSide instanceof NotFormula) {
                Formula transformedSubFormula = this.leftSide
                        .transformToConsequentsForm(!notFlag, false);
                subFormulas.add(transformedSubFormula);
            } else
                throw new RuntimeException(
                        "left side of implication is OR Formula, which isn`t valid");

        } else
            throw new RuntimeException(
                    "Unexpected Chid: left child of implies formula is not valid");

        if (isValidChild(this.rightSide)) {
            if (this.rightSide instanceof OrFormula) {

                ArrayList<Formula> disjuncts = (ArrayList<Formula>) ((OrFormula) this.rightSide)
                        .getDisjuncts();
                for (Formula disjunct : disjuncts) {
                    // remove nested OR formula
                    if (disjunct instanceof OrFormula) {
                        ArrayList<Formula> subDisjuncts = (ArrayList<Formula>) ((OrFormula) disjunct)
                                .getDisjuncts();
                        for (Formula subDisjunct : subDisjuncts) {
                            Formula transformedSubFormula = subDisjunct
                                    .transformToConsequentsForm(notFlag, false);
                            subFormulas.add(transformedSubFormula);
                        }

                    } else {
                        Formula transformedSubFormula = disjunct
                                .transformToConsequentsForm(notFlag, false);
                        subFormulas.add(transformedSubFormula);
                    }
                }
            } else if (Util.isLiteral(this.rightSide)
                    || this.rightSide instanceof NotFormula) {
                Formula transformedSubFormula = this.rightSide
                        .transformToConsequentsForm(notFlag, false);
                subFormulas.add(transformedSubFormula);
            } else
                throw new RuntimeException(
                        "rightSide side of implication is AND Formula, which isn`t valid");

        } else
            throw new RuntimeException(
                    "Unexpected Chid: right child of implies formula is not valid");

        return OrFormula.generate(subFormulas);
    }

    /**
     * Checks if a given formula is a literal, or an OR formula, an AND formula
     * or a NOT formula.
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
        if (Util.isLiteral(formula))
            return true;
        return false;
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
    public Formula tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding,
            Map<Formula, PropositionalVariable> done, int partition) {
        List<Formula> disjuncts = new ArrayList<Formula>(2);
        if (leftSide instanceof NotFormula)
            disjuncts.add(((NotFormula) leftSide).getNegatedFormula());
        else
            disjuncts.add(NotFormula.create(leftSide));
        disjuncts.add(rightSide);
        OrFormula implication = OrFormula.generate(disjuncts);
        return implication.tseitinEncode(clauses, encoding, done, partition);
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
        Formula rightSide = this.rightSide;
        Formula leftSide = this.leftSide;

        if (leftSide instanceof UninterpretedPredicateInstance)
            leftSide = ((UninterpretedPredicateInstance) leftSide)
                    .applyReplaceUninterpretedPredicates(topLeveFormula,
                            predicateInstances, instanceParameters,
                            noDependenceVars);
        else
            leftSide = leftSide.uninterpretedPredicatesToAuxiliaryVariables(
                    topLeveFormula, predicateInstances, instanceParameters,
                    noDependenceVars);

        if (rightSide instanceof UninterpretedPredicateInstance)
            rightSide = ((UninterpretedPredicateInstance) rightSide)
                    .applyReplaceUninterpretedPredicates(topLeveFormula,
                            predicateInstances, instanceParameters,
                            noDependenceVars);
        else
            rightSide = rightSide.uninterpretedPredicatesToAuxiliaryVariables(
                    topLeveFormula, predicateInstances, instanceParameters,
                    noDependenceVars);

        return ImpliesFormula.create(leftSide, rightSide);
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
        Formula rightSide = this.rightSide;
        Formula leftSide = this.leftSide;
        leftSide = leftSide.uninterpretedFunctionsToAuxiliaryVariables(
                topLeveFormula, functionInstances, instanceParameters,
                noDependenceVars);
        rightSide = rightSide.uninterpretedFunctionsToAuxiliaryVariables(
                topLeveFormula, functionInstances, instanceParameters,
                noDependenceVars);

        return ImpliesFormula.create(leftSide, rightSide);
    }

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        Formula rightSide = this.rightSide;
        Formula leftSide = this.leftSide;
        leftSide = leftSide.replaceEquivalences(topLeveFormula, replacements,
                noDependenceVars);
        rightSide = rightSide.replaceEquivalences(topLeveFormula, replacements,
                noDependenceVars);
        return ImpliesFormula.create(leftSide, rightSide);
    }

    @Override
    public Formula removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        Formula rightSide = this.rightSide;
        Formula leftSide = this.leftSide;
        leftSide = leftSide.removeDomainITE(topLevelFormula, noDependenceVars,
                andPreList);
        rightSide = rightSide.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        return ImpliesFormula.create(leftSide, rightSide);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public Formula uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars) {
        return ImpliesFormula.create(
                leftSide.uninterpretedFunctionsBackToArrayReads(arrayVars),
                rightSide.uninterpretedFunctionsBackToArrayReads(arrayVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public Formula removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        Formula newLeftSide = leftSide.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        Formula newRightSide = rightSide.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        return ImpliesFormula.create(newLeftSide, newRightSide);
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
            writer.append('(').append(SExpressionConstants.IMPLIES.toString());
            writer.append(' ');
            leftSide.writeOut(writer, tagContainer, true);
            writer.append(' ');
            rightSide.writeOut(writer, tagContainer, true);
            writer.append(')');
        }
    }

    /**
     * @throws IOException
     * @see at.iaik.suraq.smtlib.formula.Term#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.append('(').append(SExpressionConstants.IMPLIES.toString());
        writer.append(' ');
        leftSide.writeTo(writer);
        writer.append(' ');
        rightSide.writeTo(writer);
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
        leftSide.getLiterals(result, done);
        rightSide.getLiterals(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#numAigNodes(java.util.Set)
     */
    @Override
    public int numAigNodes(Set<Formula> done) {
        if (done.contains(this))
            return 0;
        int result = 0;
        result += leftSide.numAigNodes(done);
        result += rightSide.numAigNodes(done);
        result++;
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

        int left = leftSide.toAig(aigNodes, done);
        int right = rightSide.toAig(aigNodes, done);

        int result = Util.nextFreePositiveAigLiteral(aigNodes, done);

        Integer[] node = new Integer[2];
        node[0] = left;
        node[1] = right ^ 1;
        aigNodes.put(result, node);
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
        result += leftSide.size(expandDAG, done);
        result += rightSide.size(expandDAG, done);

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

        Formula[] formulas = { leftSide, rightSide };
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

        Formula[] formulas = { leftSide, rightSide };
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

        leftSide.getTerms(result, done);
        rightSide.getTerms(result, done);

        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#dependsOnlyOn(java.util.Set)
     */
    @Override
    public boolean dependsOnlyOn(Set<Formula> formulaSet) {
        if (!formulaSet.contains(leftSide))
            return false;
        if (!formulaSet.contains(rightSide))
            return false;
        return true;
    }

}
