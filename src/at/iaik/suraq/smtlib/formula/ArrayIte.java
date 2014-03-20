/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.Util;

/**
 * An if-then-else-style array term.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayIte extends ArrayTerm {

    /**
     * 
     */
    private static final long serialVersionUID = 4245403417842028322L;

    /**
     * The condition.
     */
    private final Formula condition;

    /**
     * The then-branch.
     */
    private final ArrayTerm thenBranch;

    /**
     * The else-branch
     */
    private final ArrayTerm elseBranch;

    /**
     * 
     * Constructs a new <code>ArrayIte</code>.
     * 
     * @param condition
     *            the condition
     * @param thenBranch
     *            the value of the then-branch
     * @param elseBranch
     *            the value of the else-branch
     */
    private ArrayIte(Formula condition, ArrayTerm thenBranch,
            ArrayTerm elseBranch) {
        if (condition instanceof FormulaTerm)
            this.condition = ((FormulaTerm) condition).getFormula();
        else
            this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
    }

    public static ArrayIte create(Formula condition, ArrayTerm thenBranch,
            ArrayTerm elseBranch) {
        return (ArrayIte) FormulaCache.term.put(new ArrayIte(condition,
                thenBranch, elseBranch));
    }

    /**
     * Returns the condition.
     * 
     * @return the <code>condition</code>
     */
    public Formula getCondition() {
        return condition;
    }

    /**
     * Returns the then branch.
     * 
     * @return the <code>thenBranch</code>
     */
    public ArrayTerm getThenBranch() {
        return thenBranch;
    }

    /**
     * Returns the else branch.
     * 
     * @return the <code>elseBranch</code>
     */
    public ArrayTerm getElseBranch() {
        return elseBranch;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return this; // experimental
        // return new ArrayIte(condition.deepFormulaCopy(),
        // (ArrayTerm) thenBranch.deepTermCopy(),
        // (ArrayTerm) elseBranch.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getArrayVariables(result, done);
        elseBranch.getArrayVariables(result, done);
        condition.getArrayVariables(result, done);
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
        thenBranch.getDomainVariables(result, done);
        elseBranch.getDomainVariables(result, done);
        condition.getDomainVariables(result, done);
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
        thenBranch.getPropositionalVariables(result, done);
        elseBranch.getPropositionalVariables(result, done);
        condition.getPropositionalVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getFunctionMacroNames(result, done);
        elseBranch.getFunctionMacroNames(result, done);
        condition.getFunctionMacroNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public void getFunctionMacros(Set<FunctionMacro> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getFunctionMacros(result, done);
        elseBranch.getFunctionMacros(result, done);
        condition.getFunctionMacros(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getUninterpretedFunctionNames(result, done);
        elseBranch.getUninterpretedFunctionNames(result, done);
        condition.getUninterpretedFunctionNames(result, done);
        done.add(this);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof ArrayIte))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        return ((ArrayIte) obj).thenBranch.equals(thenBranch)
                && ((ArrayIte) obj).elseBranch.equals(elseBranch)
                && ((ArrayIte) obj).condition.equals(condition);

    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return condition.hashCode() * 31 * 31 + thenBranch.hashCode() * 31
                + elseBranch.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        result.addAll(thenBranch.getIndexSet());
        result.addAll(elseBranch.getIndexSet());
        result.addAll(condition.getIndexSet());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.containsKey(this)) {
            assert (done.get(this) != null);
            assert (done.get(this) instanceof Term);
            return (Term) done.get(this);
        }
        ArrayTerm convertedThenBranch = (ArrayTerm) thenBranch.substituteTerm(
                paramMap, done);
        ArrayTerm convertedElseBranch = (ArrayTerm) elseBranch.substituteTerm(
                paramMap, done);
        Formula convertedCondition = condition
                .substituteFormula(paramMap, done);

        Term result = ArrayIte.create(convertedCondition, convertedThenBranch,
                convertedElseBranch);
        assert (result != null);
        done.put(this, result);
        return result;
    }

    /**
     * Simplifies this term by first simplifying the condition, and subsequently
     * simplifying the ite, if the condition is a constant.
     * 
     * @return a <code>ArrayIte</code> term, which is simplified. Unchanged
     *         parts are not copied.
     */
    public ArrayTerm simplify() {

        Formula simplifiedCondition = condition.simplify();

        if (simplifiedCondition instanceof PropositionalConstant)
            if (((PropositionalConstant) simplifiedCondition).getValue())
                return thenBranch;
            else
                return elseBranch;

        if (thenBranch.equals(elseBranch))
            return thenBranch;

        return ArrayIte.create(simplifiedCondition, thenBranch, elseBranch);
    }

    /**
     * @return a flattened copy of this term.
     */
    @Override
    public ArrayTerm flatten() {
        return ArrayIte.create(condition.flatten(),
                (ArrayTerm) thenBranch.flatten(),
                (ArrayTerm) elseBranch.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        SExpression[] expr = new SExpression[4];
        expr[0] = SExpressionConstants.ITE;
        expr[1] = condition.toSmtlibV2();
        expr[2] = thenBranch.toSmtlibV2();
        expr[3] = elseBranch.toSmtlibV2();
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Term arrayPropertiesToFiniteConjunctionsTerm(Set<DomainTerm> indexSet) {
        Formula condition = this.condition;
        ArrayTerm thenBranch = this.thenBranch;
        ArrayTerm elseBranch = this.elseBranch;

        condition = condition.arrayPropertiesToFiniteConjunctions(indexSet);
        thenBranch = (ArrayTerm) thenBranch
                .arrayPropertiesToFiniteConjunctionsTerm(indexSet);
        elseBranch = (ArrayTerm) elseBranch
                .arrayPropertiesToFiniteConjunctionsTerm(indexSet);

        return ArrayIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayEqualitiesTerm()
     */
    @Override
    public Term removeArrayEqualitiesTerm() {
        Formula condition = this.condition;
        ArrayTerm thenBranch = this.thenBranch;
        ArrayTerm elseBranch = this.elseBranch;

        condition = condition.removeArrayEqualities();
        thenBranch = (ArrayTerm) thenBranch.removeArrayEqualitiesTerm();
        elseBranch = (ArrayTerm) elseBranch.removeArrayEqualitiesTerm();

        return ArrayIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {

        Formula condition = this.condition;
        ArrayTerm thenBranch = this.thenBranch;
        ArrayTerm elseBranch = this.elseBranch;

        condition = condition.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);

        if (thenBranch instanceof ArrayWrite)
            thenBranch = ((ArrayWrite) thenBranch).applyWriteAxiom(
                    topLevelFormula, constraints, noDependenceVars);
        else
            thenBranch = (ArrayTerm) thenBranch.removeArrayWritesTerm(
                    topLevelFormula, constraints, noDependenceVars);

        if (elseBranch instanceof ArrayWrite)
            elseBranch = ((ArrayWrite) elseBranch).applyWriteAxiom(
                    topLevelFormula, constraints, noDependenceVars);
        else
            elseBranch = (ArrayTerm) elseBranch.removeArrayWritesTerm(
                    topLevelFormula, constraints, noDependenceVars);

        return ArrayIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(
            Set<Token> noDependenceVars) {
        Formula condition = this.condition;
        ArrayTerm thenBranch = this.thenBranch;
        ArrayTerm elseBranch = this.elseBranch;

        condition = condition
                .arrayReadsToUninterpretedFunctions(noDependenceVars);
        thenBranch = (ArrayTerm) thenBranch
                .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);
        elseBranch = (ArrayTerm) elseBranch
                .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);

        return new ArrayIte(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getUninterpretedFunctions(result, done);
        elseBranch.getUninterpretedFunctions(result, done);
        condition.getUninterpretedFunctions(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Term substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null) {
            assert (done.get(this) instanceof Term);
            return (Term) done.get(this);
        }
        Formula condition = this.condition;
        ArrayTerm thenBranch = this.thenBranch;
        ArrayTerm elseBranch = this.elseBranch;

        condition = condition.substituteUninterpretedFunction(substitutions,
                done);
        thenBranch = (ArrayTerm) thenBranch.substituteUninterpretedFunction(
                substitutions, done);
        elseBranch = (ArrayTerm) elseBranch.substituteUninterpretedFunction(
                substitutions, done);

        Term result = ArrayIte.create(condition, thenBranch, elseBranch);
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(Formula,
     *      java.util.Set, Set)
     */
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Formula condition = this.condition;
        ArrayTerm thenBranch = this.thenBranch;
        ArrayTerm elseBranch = this.elseBranch;

        condition = condition.makeArrayReadsSimple(topLevelFormula,
                constraints, noDependenceVars);
        thenBranch = (ArrayTerm) thenBranch.makeArrayReadsSimpleTerm(
                topLevelFormula, constraints, noDependenceVars);
        elseBranch = (ArrayTerm) elseBranch.makeArrayReadsSimpleTerm(
                topLevelFormula, constraints, noDependenceVars);

        return new ArrayIte(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public ArrayIte uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { return new ArrayIte(
     * condition.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars),
     * thenBranch.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars),
     * elseBranch.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars)); }
     */

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = condition.getPartitionsFromSymbols();
        partitions.addAll(thenBranch.getPartitionsFromSymbols());
        partitions.addAll(elseBranch.getPartitionsFromSymbols());

        return partitions;
    }

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        throw new RuntimeException(
                "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an ArrayIte.");

        /*
         * if (condition instanceof UninterpretedPredicateInstance) condition =
         * ((UninterpretedPredicateInstance)
         * condition).applyReplaceUninterpretedPredicates(topLeveFormula,
         * predicateInstances, instanceParameters,noDependenceVars); else
         * condition.uninterpretedPredicatesToAuxiliaryVariables(
         * topLeveFormula, predicateInstances, instanceParameters,
         * noDependenceVars);
         * 
         * thenBranch.uninterpretedPredicatesToAuxiliaryVariables(
         * topLeveFormula, predicateInstances, instanceParameters,
         * noDependenceVars);
         * 
         * elseBranch.uninterpretedPredicatesToAuxiliaryVariables(
         * topLeveFormula, predicateInstances, instanceParameters,
         * noDependenceVars);
         */
    }

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        throw new RuntimeException(
                "uninterpretedFunctionsToAuxiliaryVariables cannot be called on an ArrayIte.");

        /*
         * condition.uninterpretedFunctionsToAuxiliaryVariables( topLeveFormula,
         * functionInstances, instanceParameters, noDependenceVars);
         * thenBranch.uninterpretedFunctionsToAuxiliaryVariables(
         * topLeveFormula, functionInstances, instanceParameters,
         * noDependenceVars);
         * elseBranch.uninterpretedFunctionsToAuxiliaryVariables(
         * topLeveFormula, functionInstances, instanceParameters,
         * noDependenceVars);
         */
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.ArrayTerm#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public ArrayTerm uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars) {
        return ArrayIte.create(
                condition.uninterpretedFunctionsBackToArrayReads(arrayVars),
                thenBranch.uninterpretedFunctionsBackToArrayReads(arrayVars),
                elseBranch.uninterpretedFunctionsBackToArrayReads(arrayVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeDomainITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.List)
     */
    @Override
    public ArrayTerm removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        Formula newCondition = condition.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        ArrayTerm newThenBranch = thenBranch.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        ArrayTerm newElseBranch = elseBranch.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        return ArrayIte.create(newCondition, newThenBranch, newElseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.ArrayTerm#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public ArrayVariable removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        Token newToken = Token.generate(Util.freshVarNameCached(
                topLevelFormula, "array_itev"));
        ArrayVariable newVar = ArrayVariable.create(newToken);

        List<ArrayTerm> termsThen = new ArrayList<ArrayTerm>(2);
        List<ArrayTerm> termsElse = new ArrayList<ArrayTerm>(2);
        termsThen.add(newVar);
        termsThen.add(thenBranch.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints));
        termsElse.add(newVar);
        termsElse.add(elseBranch.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints));
        try {
            ArrayEq eqThen = (ArrayEq) EqualityFormula.create(termsThen, true);
            ArrayEq eqElse = (ArrayEq) EqualityFormula.create(termsElse, true);
            PropositionalIte propIte = PropositionalIte.create(condition
                    .removeArrayITE(topLevelFormula, noDependenceVars,
                            constraints), eqThen, eqElse);
            // if (Util.formulaContainsAny(propIte, noDependenceVars))
            // Always make new auxiliary variables noDep to avoid combinational
            // loops
            noDependenceVars.add(newToken);
            constraints.add(propIte);
            return newVar;
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected exception while removing DomainITEs.", exc);
        }
    }

    /**
     * @throws IOException
     * @see at.iaik.suraq.smtlib.formula.Term#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.append('(').append(SExpressionConstants.ITE.toString());
        writer.append(' ');
        condition.writeTo(writer);
        writer.append(' ');
        thenBranch.writeTo(writer);
        writer.append(' ');
        elseBranch.writeTo(writer);
        writer.append(')');

    }

}
