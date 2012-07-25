/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

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
    private ArrayTerm thenBranch;

    /**
     * The else-branch
     */
    private ArrayTerm elseBranch;

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
    public ArrayIte(Formula condition, ArrayTerm thenBranch,
            ArrayTerm elseBranch) {
        if (condition instanceof FormulaTerm)
            this.condition = ((FormulaTerm) condition).getFormula();
        else
            this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
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
        return new ArrayIte(condition.deepFormulaCopy(),
                (ArrayTerm) thenBranch.deepTermCopy(),
                (ArrayTerm) elseBranch.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = thenBranch.getArrayVariables();
        result.addAll(elseBranch.getArrayVariables());
        result.addAll(condition.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = thenBranch.getDomainVariables();
        result.addAll(elseBranch.getDomainVariables());
        result.addAll(condition.getDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> result = thenBranch
                .getPropositionalVariables();
        result.addAll(elseBranch.getPropositionalVariables());
        result.addAll(condition.getPropositionalVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = thenBranch.getFunctionMacroNames();
        result.addAll(elseBranch.getFunctionMacroNames());
        result.addAll(condition.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = thenBranch.getFunctionMacros();
        result.addAll(elseBranch.getFunctionMacros());
        result.addAll(condition.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = thenBranch.getUninterpretedFunctionNames();
        result.addAll(elseBranch.getUninterpretedFunctionNames());
        result.addAll(condition.getUninterpretedFunctionNames());
        return result;
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
    public Term substituteTerm(Map<Token, ? extends Term> paramMap) {
        ArrayTerm convertedThenBranch = (ArrayTerm) thenBranch
                .substituteTerm(paramMap);
        ArrayTerm convertedElseBranch = (ArrayTerm) elseBranch
                .substituteTerm(paramMap);
        Formula convertedCondition = condition.substituteFormula(paramMap);
        return new ArrayIte(convertedCondition, convertedThenBranch,
                convertedElseBranch);
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

        return new ArrayIte(simplifiedCondition, thenBranch, elseBranch);
    }

    /**
     * @return a flattened copy of this term.
     */
    @Override
    public ArrayTerm flatten() {
        return new ArrayIte(condition.flatten(),
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
        thenBranch = (ArrayTerm) thenBranch.arrayPropertiesToFiniteConjunctionsTerm(indexSet);
        elseBranch = (ArrayTerm) elseBranch.arrayPropertiesToFiniteConjunctionsTerm(indexSet);
        
        return new ArrayIte(condition, thenBranch, elseBranch);
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
        
        return new ArrayIte(condition, thenBranch, elseBranch);
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

        return new ArrayIte(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(Set<Token> noDependenceVars) {
        Formula condition = this.condition;
        ArrayTerm thenBranch = this.thenBranch;
        ArrayTerm elseBranch = this.elseBranch;
        
        condition = condition.arrayReadsToUninterpretedFunctions(noDependenceVars);
        thenBranch = (ArrayTerm) thenBranch.arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);
        elseBranch = (ArrayTerm) elseBranch.arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);
        
        return new ArrayIte(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = thenBranch
                .getUninterpretedFunctions();
        result.addAll(elseBranch.getUninterpretedFunctions());
        result.addAll(condition.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Term substituteUninterpretedFunctionTerm(Token oldFunction,
            UninterpretedFunction newFunction) {
        Formula condition = this.condition;
        ArrayTerm thenBranch = this.thenBranch;
        ArrayTerm elseBranch = this.elseBranch;
        
        condition = condition.substituteUninterpretedFunction(oldFunction, newFunction);
        thenBranch = (ArrayTerm) thenBranch.substituteUninterpretedFunctionTerm(oldFunction, newFunction);
        elseBranch = (ArrayTerm) elseBranch.substituteUninterpretedFunctionTerm(oldFunction, newFunction);
        
        return new ArrayIte(condition, thenBranch, elseBranch);
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
    /*@Override
    public ArrayIte uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new ArrayIte(
                condition.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars),
                thenBranch.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars),
                elseBranch.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars));
    }*/

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
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
       	
    		throw new RuntimeException(
                "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an ArrayIte.");
    	
    	    /*
    		if (condition instanceof UninterpretedPredicateInstance)
    		  condition = ((UninterpretedPredicateInstance) condition).applyReplaceUninterpretedPredicates(topLeveFormula,
					      predicateInstances, instanceParameters,noDependenceVars);
			else
			  condition.uninterpretedPredicatesToAuxiliaryVariables(
						  topLeveFormula, predicateInstances, instanceParameters, noDependenceVars); 
    		
    		thenBranch.uninterpretedPredicatesToAuxiliaryVariables(
                topLeveFormula, predicateInstances, instanceParameters, noDependenceVars);
    		
            elseBranch.uninterpretedPredicatesToAuxiliaryVariables(
                topLeveFormula, predicateInstances, instanceParameters, noDependenceVars);
            */
    }
    
    
    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars){
    	
    		throw new RuntimeException(
                "uninterpretedFunctionsToAuxiliaryVariables cannot be called on an ArrayIte.");
    		
    	/* condition.uninterpretedFunctionsToAuxiliaryVariables(
                 topLeveFormula, functionInstances, instanceParameters, noDependenceVars);
         thenBranch.uninterpretedFunctionsToAuxiliaryVariables(
                 topLeveFormula, functionInstances, instanceParameters, noDependenceVars);
         elseBranch.uninterpretedFunctionsToAuxiliaryVariables(
                 topLeveFormula, functionInstances, instanceParameters, noDependenceVars);
                 */
    }
    
}
