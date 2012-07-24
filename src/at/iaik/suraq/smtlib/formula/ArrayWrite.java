/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.Util;

/**
 * An array write expression.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayWrite extends ArrayTerm {

    /**
     * 
     */
    private static final long serialVersionUID = -2087596963751666011L;

    /**
     * The array to which this expression writes.
     */
    private final ArrayTerm arrayTerm;

    /**
     * The index to which this expression writes.
     */
    private DomainTerm indexTerm;

    /**
     * The value that is written.
     */
    private DomainTerm valueTerm;

    /**
     * Constructs a new <code>ArrayWrite</code>.
     * 
     * @param arrayTerm
     *            the array to which is written.
     * @param indexTerm
     *            the index to which is written.
     * @param valueTerm
     *            the value being written.
     */
    public ArrayWrite(ArrayTerm arrayTerm, DomainTerm indexTerm,
            DomainTerm valueTerm) {
        this.arrayTerm = arrayTerm;
        this.indexTerm = indexTerm;
        this.valueTerm = valueTerm;
    }

    /**
     * Returns the array to which is written.
     * 
     * @return the <code>arrayTerm</code>
     */
    public ArrayTerm getArrayTerm() {
        return arrayTerm;
    }

    /**
     * Returns the index to which is written.
     * 
     * @return the <code>indexTerm</code>
     */
    public DomainTerm getIndexTerm() {
        return indexTerm;
    }

    /**
     * Returns the value being written.
     * 
     * @return the <code>valueTerm</code>
     */
    public DomainTerm getValueTerm() {
        return valueTerm;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return new ArrayWrite((ArrayTerm) arrayTerm.deepTermCopy(),
                indexTerm.deepTermCopy(), valueTerm.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = arrayTerm.getArrayVariables();
        result.addAll(indexTerm.getArrayVariables());
        result.addAll(valueTerm.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = arrayTerm.getDomainVariables();
        result.addAll(indexTerm.getDomainVariables());
        result.addAll(valueTerm.getDomainVariables());
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
        result.addAll(valueTerm.getPropositionalVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = arrayTerm.getFunctionMacroNames();
        result.addAll(indexTerm.getFunctionMacroNames());
        result.addAll(valueTerm.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = arrayTerm.getFunctionMacros();
        result.addAll(indexTerm.getFunctionMacros());
        result.addAll(valueTerm.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = arrayTerm.getUninterpretedFunctionNames();
        result.addAll(indexTerm.getUninterpretedFunctionNames());
        result.addAll(valueTerm.getUninterpretedFunctionNames());
        return result;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof ArrayWrite))
            return false;

        if (this.hashCode() != obj.hashCode())
            return false;

        return ((ArrayWrite) obj).arrayTerm.equals(arrayTerm)
                && ((ArrayWrite) obj).indexTerm.equals(indexTerm)
                && ((ArrayWrite) obj).valueTerm.equals(valueTerm);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return arrayTerm.hashCode() * 31 * 31 + indexTerm.hashCode() * 31
                + valueTerm.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        throw new SuraqException(
                "Encountered array write while computing index set.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap) {
        return new ArrayWrite((ArrayTerm) arrayTerm.substituteTerm(paramMap),
                (DomainTerm) indexTerm.substituteTerm(paramMap),
                (DomainTerm) valueTerm.substituteTerm(paramMap));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        SExpression[] expr = new SExpression[4];
        expr[0] = SExpressionConstants.STORE;
        expr[1] = arrayTerm.toSmtlibV2();
        expr[2] = indexTerm.toSmtlibV2();
        expr[3] = valueTerm.toSmtlibV2();
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        arrayTerm.arrayPropertiesToFiniteConjunctions(indexSet);
        indexTerm.arrayPropertiesToFiniteConjunctions(indexSet);
        valueTerm.arrayPropertiesToFiniteConjunctions(indexSet);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        arrayTerm.removeArrayEqualities();
        indexTerm.removeArrayEqualities();
        valueTerm.removeArrayEqualities();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        throw new RuntimeException(
                "removeArrayWrites cannot be called on an ArrayWrite.\nUse applyWriteAxiom instead.");

    }

    /**
     * Applies the write axiom to this <code>ArrayWrite</code> term. I.e.,
     * returns a (fresh) <code>ArrayVariable</code> to be used instead of this
     * term.
     * 
     * @param topLevelFormula
     *            the top-level formula (w.r.t. which fresh names are selected)
     * @param constraints
     *            A set of formulas to which the constraints of the write
     *            axiom's application will be added.
     * @return an <code>ArrayVariable</code> with a fresh name.
     */
    public ArrayVariable applyWriteAxiom(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {

        ArrayVariable result;
        DomainTerm index;
        DomainTerm value;

        // First, recursively remove writes from sub-parts
        if (arrayTerm instanceof ArrayWrite)
            result = ((ArrayWrite) arrayTerm).applyWriteAxiom(topLevelFormula,
                    constraints, noDependenceVars);
        else {
            assert (arrayTerm instanceof ArrayVariable);
            result = (ArrayVariable) arrayTerm;
        }

        index = indexTerm.deepTermCopy();
        index.removeArrayWrites(topLevelFormula, constraints, noDependenceVars);
        if (!(index instanceof DomainVariable)) {
            DomainVariable simpleIndex = new DomainVariable(Util.freshVarName(
                    topLevelFormula, "read"));
            List<DomainTerm> terms = new ArrayList<DomainTerm>();
            terms.add(simpleIndex);
            terms.add(index);
            constraints.add(new DomainEq(terms, true));

            // Check if the complex index contained any noDependenceVars.
            // This might be conservative and might not be complete (i.e., may
            // result unnecessary unrealizability)
            if (Util.termContainsAny(index, noDependenceVars))
                noDependenceVars.add(new Token(simpleIndex.getVarName()));
            index = simpleIndex;
        }

        value = valueTerm.deepTermCopy();
        value.removeArrayWrites(topLevelFormula, constraints, noDependenceVars);

        // now apply axiom
        String oldVar = result.toSmtlibV2().toString().replaceAll("\\W", "");
        ArrayVariable newVar = new ArrayVariable(Util.freshVarName(
                topLevelFormula, oldVar + "_store"));

        ArrayRead newRead = new ArrayRead(newVar, index);
        newRead.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        value.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        Set<DomainTerm> domainTerms = new HashSet<DomainTerm>();
        domainTerms.add(newRead);
        domainTerms.add(value);
        constraints.add(new DomainEq(domainTerms, true));

        DomainVariable newUVar = new DomainVariable(Util.freshVarName(
                topLevelFormula, "uVar"));
        domainTerms.clear();
        domainTerms.add(index);
        domainTerms.add(newUVar);
        Formula indexGuard = new DomainEq(domainTerms, false);

        domainTerms.clear();
        domainTerms.add(new ArrayRead(newVar, newUVar));
        domainTerms.add(new ArrayRead(result, newUVar));
        Formula valueConstraint = new DomainEq(domainTerms, true);

        Set<DomainVariable> uVars = new HashSet<DomainVariable>();
        uVars.add(newUVar);
        try {
            constraints.add(new ArrayProperty(uVars, indexGuard,
                    valueConstraint));
        } catch (SuraqException exc) {
            throw new RuntimeException("Could not apply write axiom.", exc);
        }

        // Make the new array a noDependenceVar
        // (store-results are "future" values, on which we should not depend.)
        noDependenceVars.add(new Token(newVar.getVarName()));

        return newVar;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        arrayTerm.arrayReadsToUninterpretedFunctions(noDependenceVars);

        if (indexTerm instanceof ArrayRead)
            indexTerm = ((ArrayRead) indexTerm)
                    .toUninterpretedFunctionInstance(noDependenceVars);
        else
            indexTerm.arrayReadsToUninterpretedFunctions(noDependenceVars);

        if (valueTerm instanceof ArrayRead)
            valueTerm = ((ArrayRead) valueTerm)
                    .toUninterpretedFunctionInstance(noDependenceVars);
        else
            valueTerm.arrayReadsToUninterpretedFunctions(noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = arrayTerm
                .getUninterpretedFunctions();
        result.addAll(indexTerm.getUninterpretedFunctions());
        result.addAll(valueTerm.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        arrayTerm.substituteUninterpretedFunction(oldFunction, newFunction);
        indexTerm.substituteUninterpretedFunction(oldFunction, newFunction);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#flatten()
     */
    @Override
    public Term flatten() {
        return new ArrayWrite((ArrayTerm) arrayTerm.flatten(),
                (DomainTerm) indexTerm.flatten(),
                (DomainTerm) valueTerm.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, Set)
     */
    @Override
    public void makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        arrayTerm.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        indexTerm.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        valueTerm.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.ArrayTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*@Override
    public ArrayTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new ArrayWrite(
                arrayTerm.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars),
                indexTerm.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars),
                valueTerm.uninterpretedPredicatesToAuxiliaryVariables(
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
        partitions.addAll(valueTerm.getPartitionsFromSymbols());

        return partitions;
    }
    


    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public void uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {  	
    	
       	throw new RuntimeException(
                "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an ArrayWrite.");
       	
       	/*
		        arrayTerm.uninterpretedPredicatesToAuxiliaryVariables(
		                topLeveFormula, predicateInstances, instanceParameters, noDependenceVars);
		        indexTerm.uninterpretedPredicatesToAuxiliaryVariables(
		                topLeveFormula, predicateInstances, instanceParameters, noDependenceVars);
		        valueTerm.uninterpretedPredicatesToAuxiliaryVariables(
		                topLeveFormula, predicateInstances, instanceParameters, noDependenceVars);*/
    }
    
    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public void uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
    	  	
       	throw new RuntimeException(
                "uninterpretedFunctionsToAuxiliaryVariables cannot be called on an ArrayWrite.");
       	
                /*arrayTerm.uninterpretedFunctionsToAuxiliaryVariables(
                        topLeveFormula, functionInstances, instanceParameters, noDependenceVars);
                indexTerm.uninterpretedFunctionsToAuxiliaryVariables(
                        topLeveFormula, functionInstances, instanceParameters,noDependenceVars);
                valueTerm.uninterpretedFunctionsToAuxiliaryVariables(
                        topLeveFormula, functionInstances, instanceParameters, noDependenceVars);*/
    }  
}
