/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.Util;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayRead extends DomainTerm {

    /**
     * 
     */
    private static final long serialVersionUID = -2549087326175334824L;

    /**
     * The array variable that is read.
     */
    private final ArrayTerm arrayTerm;

    /**
     * The index from which is read.
     */
    private final DomainTerm indexTerm;

    /**
     * Constructs a new <code>ArrayRead</code>.
     * 
     * @param arrayTerm
     *            the variable that is read
     * @param index
     *            the index from which is read.
     */
    public ArrayRead(ArrayTerm arrayTerm, DomainTerm index) {
        super();
        this.arrayTerm = arrayTerm;
        this.indexTerm = index;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        // not applicable for ArrayRead.
        return false;
    }

    /**
     * Returns the index from which is read.
     * 
     * @return the index from which is read.
     */
    public DomainTerm getIndexTerm() {
        return indexTerm;
    }

    /**
     * Returns the array variable from which is read.
     * 
     * @return the array variable from which is read.
     */
    public ArrayTerm getArrayTerm() {
        return arrayTerm;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public DomainTerm deepTermCopy() {
        return new ArrayRead((ArrayTerm) arrayTerm.deepTermCopy(),
                indexTerm.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = arrayTerm.getArrayVariables();
        result.addAll(indexTerm.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = arrayTerm.getDomainVariables();
        result.addAll(indexTerm.getDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> result = arrayTerm
                .getPropositionalVariables();
        result.addAll(indexTerm.getPropositionalVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = arrayTerm.getFunctionMacroNames();
        result.addAll(indexTerm.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = arrayTerm.getFunctionMacros();
        result.addAll(indexTerm.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = arrayTerm.getUninterpretedFunctionNames();
        result.addAll(indexTerm.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof ArrayRead))
            return false;

        if (this.hashCode() != obj.hashCode())
            return false;

        return arrayTerm.equals(((ArrayRead) obj).arrayTerm)
                && indexTerm.equals(((ArrayRead) obj).indexTerm);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return arrayTerm.hashCode() * 31 + indexTerm.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        if (!(arrayTerm instanceof ArrayVariable))
            throw new SuraqException(
                    "Encountered array-read from non-variable array term while computing index set.");
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        result.add(indexTerm);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap) {
        return new ArrayRead((ArrayTerm) arrayTerm.substituteTerm(paramMap),
                (DomainTerm) indexTerm.substituteTerm(paramMap));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        SExpression[] expr = new SExpression[3];
        expr[0] = SExpressionConstants.SELECT;
        expr[1] = arrayTerm.toSmtlibV2();
        expr[2] = indexTerm.toSmtlibV2();
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Term arrayPropertiesToFiniteConjunctionsTerm(Set<DomainTerm> indexSet) {
        ArrayTerm arrayTerm = (ArrayTerm)this.arrayTerm.arrayPropertiesToFiniteConjunctionsTerm(indexSet);
        DomainTerm indexTerm = (DomainTerm)this.indexTerm.arrayPropertiesToFiniteConjunctionsTerm(indexSet);
        return new ArrayRead(arrayTerm,indexTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayEqualitiesTerm()
     */
    @Override
    public Term removeArrayEqualitiesTerm() {
        ArrayTerm arrayTerm = (ArrayTerm)this.arrayTerm.removeArrayEqualitiesTerm();
        DomainTerm indexTerm = (DomainTerm)this.indexTerm.removeArrayEqualitiesTerm();
        return new ArrayRead(arrayTerm, indexTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        ArrayTerm arrayTerm = this.arrayTerm;
        DomainTerm indexTerm = this.indexTerm;

        if (arrayTerm instanceof ArrayWrite)
            arrayTerm = ((ArrayWrite) arrayTerm).applyWriteAxiom(
                    topLevelFormula, constraints, noDependenceVars);
        else
            arrayTerm = (ArrayTerm) arrayTerm.removeArrayWritesTerm(
                    topLevelFormula, constraints, noDependenceVars);

        indexTerm = (DomainTerm) indexTerm.removeArrayWritesTerm(topLevelFormula,
                constraints, noDependenceVars);

        return new ArrayRead(arrayTerm, indexTerm);
    }

    /**
     * Returns an <code>UninterpretedFunctionInstance</code> that is
     * "equivalent" to this <code>ArrayRead</code>.
     * 
     * @return an <code>UninterpretedFunctionInstance</code> that is
     *         "equivalent" to this <code>ArrayRead</code>.
     */
    public UninterpretedFunctionInstance toUninterpretedFunctionInstance(
            Set<Token> noDependenceVars) {
        try {
            String functionName = arrayTerm.toSmtlibV2().toString()
                    .replaceAll("\\W", "");

            DomainTerm term = indexTerm;

            if (term instanceof ArrayRead)
                term = ((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars);
            else
                term = (DomainTerm) term.arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);

            // Check if the arrayTerm contained any noDependenceVars.
            // This is conservative and might not be complete (i.e., may
            // result unnecessary unrealizability), but
            // in practice, array reads should only occur on primitive
            // array expressions, so this should not be a "real" problem.
            if (Util.termContainsAny(arrayTerm, noDependenceVars))
                noDependenceVars.add(Token.generate(functionName));

            return new UninterpretedFunctionInstance(new UninterpretedFunction(
                    functionName, 1, SExpressionConstants.VALUE_TYPE), term);
        } catch (WrongNumberOfParametersException exc) {
            throw new RuntimeException(
                    "Could not replace array-reads with uninterpreted functions",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(Set<Token> noDependenceVars) {
        throw new RuntimeException(
                "arrayReadsToUninterpretedFunctions cannot be called on an ArrayWrite.\nUse toUninterpretedFunctionInstance instead.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = arrayTerm
                .getUninterpretedFunctions();
        result.addAll(indexTerm.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Term substituteUninterpretedFunctionTerm(Token oldFunction,
            UninterpretedFunction newFunction) {
        ArrayTerm arrayTerm = (ArrayTerm) this.arrayTerm
                .substituteUninterpretedFunctionTerm(oldFunction, newFunction);
        DomainTerm indexTerm = (DomainTerm) this.indexTerm
                .substituteUninterpretedFunctionTerm(oldFunction, newFunction);
        return new ArrayRead(arrayTerm, indexTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#flatten()
     */
    @Override
    public Term flatten() {
        return new ArrayRead((ArrayTerm) arrayTerm.flatten(),
                (DomainTerm) indexTerm.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(Formula,
     *      java.util.Set, Set)
     */
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        if (this.indexTerm instanceof DomainVariable)
            return this; // This read is already simple.

        DomainTerm oldIndexTerm = this.indexTerm;
        DomainTerm indexTerm = DomainVariable.create(Util.freshVarName(
                topLevelFormula, "read"));

        List<DomainTerm> list = new ArrayList<DomainTerm>();
        list.add(indexTerm);
        list.add(oldIndexTerm);
        constraints.add(new DomainEq(list, true));

        // Check if the arrayTerm contained any noDependenceVars.
        // This is conservative and might not be complete (i.e., may
        // result unnecessary unrealizability), but
        // in practice, array reads should only occur on primitive
        // array expressions, so this should not be a "real" problem.
        if (Util.termContainsAny(arrayTerm, noDependenceVars))
            noDependenceVars.add(Token.generate(((DomainVariable) indexTerm)
                    .getVarName()));

        return new ArrayRead(this.arrayTerm, indexTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*@Override
    public DomainTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {

        return new ArrayRead(
                arrayTerm.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars),
                indexTerm.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars));

    }*/

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = arrayTerm.getPartitionsFromSymbols();
        partitions.addAll(indexTerm.getPartitionsFromSymbols());

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
                "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an ArrayRead.");
    	
    	/*arrayTerm.uninterpretedPredicatesToAuxiliaryVariables(
                topLeveFormula, predicateInstances, instanceParameters, noDependenceVars);
        indexTerm.uninterpretedPredicatesToAuxiliaryVariables(
                topLeveFormula, predicateInstances, instanceParameters, noDependenceVars);*/
    }
    
    
    
    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {     
    	
    	throw new RuntimeException(
                "uninterpretedFunctionsToAuxiliaryVariables cannot be called on an ArrayRead.");
               /* arrayTerm.uninterpretedFunctionsToAuxiliaryVariables(
                        topLeveFormula, functionInstances, instanceParameters, noDependenceVars);
                indexTerm.uninterpretedFunctionsToAuxiliaryVariables(
                        topLeveFormula, functionInstances, instanceParameters, noDependenceVars);*/
    }
    
}
