/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TermFunctionMacroInstance extends DomainTerm {
    /**
     * 
     */
    private static final long serialVersionUID = -2357506879919697251L;

    /**
     * The macro of which this is an instance.
     */
    private final TermFunctionMacro macro;

    /**
     * A map from parameter names to the terms.
     */
    private final Map<Token, Term> paramMap;

    /**
     * Constructs a new <code>TermFunctionMacroInstance</code>.
     * 
     * @param macro
     *            the function macro of which this will be an instance.
     * @param paramMap
     *            the map from parameter names to their terms
     * @throws InvalidParametersException
     *             if the given map either misses a parameter or the type of the
     *             term in the map disagrees with the macro.
     */
    public TermFunctionMacroInstance(TermFunctionMacro macro,
            Map<Token, Term> paramMap) throws InvalidParametersException {

        for (Token parameter : macro.getParameters()) {
            if (!paramMap.containsKey(parameter))
                throw new InvalidParametersException(
                        "Given map misses parameter " + parameter.toString());
            if (!paramMap.get(parameter).getType()
                    .equals(macro.getParamType(parameter)))
                throw new InvalidParametersException(
                        "Type mismatch for parameter " + parameter.toString());
        }

        this.macro = macro;
        this.paramMap = paramMap;
    }

    /**
     * Returns the macro of which this is an instance.
     * 
     * @return the <code>macro</code>
     */
    public TermFunctionMacro getMacro() {
        return macro;
    }

    /**
     * Returns the term corresponding to the parameter <code>token</code>.
     * 
     * @param token
     *            the token identifying the parameter of which the term should
     *            be returned.
     * @return the term mapped to by the given token.
     */
    public Term getTerm(Token token) {
        return paramMap.get(token);
    }

    /**
     * Returns a copy of the parameter map.
     * 
     * @return the <code>paramMap</code>
     */
    public Map<Token, Term> getParamMap() {
        return new HashMap<Token, Term>(paramMap);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getType()
     */
    @Override
    public SExpression getType() {
        return macro.getType();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public DomainTerm deepTermCopy() {
        TermFunctionMacro macro = new TermFunctionMacro(this.macro);
        Map<Token, Term> paramMap = new HashMap<Token, Term>();
        for (Token token : this.paramMap.keySet())
            paramMap.put((Token) token.deepCopy(), this.paramMap.get(token)
                    .deepTermCopy());

        try {
            return new TermFunctionMacroInstance(macro, paramMap);
        } catch (InvalidParametersException exc) {
            // This should never happen!
            assert (false);
            throw new RuntimeException(
                    "Unexpected situation while copying function macro instance.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Term term : paramMap.values())
            variables.addAll(term.getArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Term term : paramMap.values())
            variables.addAll(term.getDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Term term : paramMap.values())
            variables.addAll(term.getPropositionalVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> macroNames = new HashSet<String>();
        macroNames.add(macro.getName().toString());
        for (Term term : paramMap.values())
            macroNames.addAll(term.getFunctionMacroNames());
        macroNames.addAll(macro.getBody().getFunctionMacroNames());
        return macroNames;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
        macros.add(macro);
        for (Term term : paramMap.values())
            macros.addAll(term.getFunctionMacros());
        macros.addAll(macro.getBody().getFunctionMacros());
        return macros;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof PropositionalFunctionMacroInstance))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        if (!((TermFunctionMacroInstance) obj).macro.equals(macro))
            return false;
        if (!((TermFunctionMacroInstance) obj).paramMap.equals(paramMap))
            return false;
        return true;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return macro.hashCode() * 31 + paramMap.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> functionNames = new HashSet<String>();
        functionNames.addAll(macro.getBody().getUninterpretedFunctionNames());
        for (Term term : paramMap.values())
            functionNames.addAll(term.getUninterpretedFunctionNames());
        return functionNames;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap) {
        Map<Token, Term> convertedMap = new HashMap<Token, Term>();

        for (Token token : this.paramMap.keySet())
            convertedMap.put(token,
                    this.paramMap.get(token).substituteTerm(paramMap));

        try {
            return new TermFunctionMacroInstance(macro, convertedMap);
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpected exception while converting TermFunctionMacroInstance to caller scope.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> localIndexSet = macro.getBody().getIndexSet();
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        for (DomainTerm term : localIndexSet) {
            result.add((DomainTerm) term.substituteTerm(paramMap));
        }
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> expr = new ArrayList<SExpression>();
        expr.add(macro.getName());
        for (Token param : macro.getParameters())
            expr.add(paramMap.get(param).toSmtlibV2());
        return new SExpression(expr);
    }

    /**
     * Removes array equalities from the body of the macro.
     */
    @Override
    public Term removeArrayEqualitiesTerm() {
        TermFunctionMacro macro = (TermFunctionMacro) this.macro
                .removeArrayEqualities();
        Map<Token, Term> paramMap = new HashMap<Token, Term>();

        for (Token token : paramMap.keySet())
            paramMap.put(token, this.paramMap.get(token)
                    .removeArrayEqualitiesTerm());

        try {
            return new TermFunctionMacroInstance(macro, paramMap);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * Converts array properties in the body of the macro to finite conjunctions
     * 
     * @param indexSet
     *            the index set.
     */
    @Override
    public Term arrayPropertiesToFiniteConjunctionsTerm(Set<DomainTerm> indexSet) {
        TermFunctionMacro macro = (TermFunctionMacro) this.macro
                .arrayPropertiesToFiniteConjunctions(indexSet);
        Map<Token, Term> paramMap = new HashMap<Token, Term>();
        
        for (Token token : paramMap.keySet())
            paramMap.put(token, this.paramMap.get(token)
                    .arrayPropertiesToFiniteConjunctionsTerm(indexSet));

        try {
            return new TermFunctionMacroInstance(macro, paramMap);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Set<Formula> localConstraints = macro.removeArrayWrites(
                topLevelFormula, noDependenceVars);
        for (Formula localConstraint : localConstraints)
            constraints.add(localConstraint.substituteFormula(paramMap));
        for (Term term : paramMap.values())
            term.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        macro.arrayReadsToUninterpretedFunctions(noDependenceVars);
        for (Token key : paramMap.keySet()) {
            Term term = paramMap.get(key);
            if (term instanceof ArrayRead)
                paramMap.put(key, ((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars));
            else
                term.arrayReadsToUninterpretedFunctions(noDependenceVars);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return macro.getUninterpretedFunctions();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Term substituteUninterpretedFunctionTerm(Token oldFunction,
            UninterpretedFunction newFunction) {
        TermFunctionMacro macro = (TermFunctionMacro) this.macro.substituteUninterpretedFunction(oldFunction, newFunction);
        
        Map<Token, Term> paramMap = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet())
            paramMap.put(token, this.paramMap.get(token).substituteUninterpretedFunctionTerm(oldFunction, newFunction));
        

        try {
            return new TermFunctionMacroInstance(macro, paramMap);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Term flatten() {
        return macro.getBody().substituteTerm(paramMap).flatten();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        return ((DomainTerm) this.flatten()).isEvar(uVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Set<Formula> localConstraints = macro.makeArrayReadsSimple(
                topLevelFormula, noDependenceVars);
        for (Formula localConstraint : localConstraints)
            constraints.add(localConstraint.substituteFormula(paramMap));
        for (Term term : paramMap.values())
            term.makeArrayReadsSimple(topLevelFormula, constraints,
                    noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*@Override
    public DomainTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        Set<Formula> localConstraints = new HashSet<Formula>();
        TermFunctionMacro newMacro = macro
                .uninterpretedPredicatesToAuxiliaryVariables(topLeveFormula,
                        localConstraints, noDependenceVars);
        for (Formula localConstraint : localConstraints)
            constraints.add(localConstraint.substituteFormula(paramMap));

        Map<Token, Term> newParamMap = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet())
            newParamMap.put(
                    token,
                    paramMap.get(token)
                            .uninterpretedPredicatesToAuxiliaryVariables(
                                    topLeveFormula, constraints,
                                    noDependenceVars));
        try {
            return new TermFunctionMacroInstance(newMacro, newParamMap);
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpectedly unable to create TermFunctionMacroInstance.",
                    exc);
        }
    }*/

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = macro.getAssertPartition();

        for (Term term : paramMap.values())
            partitions.addAll(term.getPartitionsFromSymbols());

        return partitions;
    }
    
    
    
    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    public void uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
        
	        macro.uninterpretedPredicatesToAuxiliaryVariables(topLeveFormula,
	        		predicateInstances, instanceParameters, noDependenceVars);
	      
	        for (Token token : paramMap.keySet())
	                    paramMap.get(token)
	                            .uninterpretedPredicatesToAuxiliaryVariables(
	                                    topLeveFormula, predicateInstances,
	                                    instanceParameters, noDependenceVars);
    }
    
      
    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {

	        macro.uninterpretedFunctionsToAuxiliaryVariables(topLeveFormula,
	                		functionInstances, instanceParameters, noDependenceVars);
   
	        for (Token token : paramMap.keySet())
	                   paramMap.get(token)
	                            .uninterpretedFunctionsToAuxiliaryVariables(
	                                    topLeveFormula, functionInstances,
	                                    instanceParameters, noDependenceVars);
    }
}
