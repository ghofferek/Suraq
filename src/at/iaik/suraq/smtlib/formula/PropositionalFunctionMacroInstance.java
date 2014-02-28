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

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.HashTagContainer;
import at.iaik.suraq.util.ImmutableHashMap;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalFunctionMacroInstance implements Formula {

    /**
     * 
     */
    private static final long serialVersionUID = 5604001861879637266L;

    /**
     * The macro of which this is an instance.
     */
    private final PropositionalFunctionMacro macro;

    /**
     * A map from parameter names to the terms.
     */
    private final ImmutableHashMap<Token, Term> paramMap;

    /**
     * Constructs a new <code>PropositionalFunctionMacroInstance</code>.
     * 
     * @param macro
     *            the function macro of which this will be an instance.
     * @param paramMap
     *            the map from parameter names to their terms
     * @throws InvalidParametersException
     *             if the given map either misses a parameter or the type of the
     *             term in the map disagrees with the macro.
     */
    private PropositionalFunctionMacroInstance(
            PropositionalFunctionMacro macro, Map<Token, Term> paramMap)
            throws InvalidParametersException {

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
        this.paramMap = new ImmutableHashMap<Token, Term>(paramMap);
    }

    public static PropositionalFunctionMacroInstance create(
            PropositionalFunctionMacro macro, Map<Token, Term> paramMap)
            throws InvalidParametersException {
        return (PropositionalFunctionMacroInstance) FormulaCache.formula
                .put(new PropositionalFunctionMacroInstance(macro, paramMap));
    }

    /**
     * Returns the macro of which this is an instance.
     * 
     * @return the <code>macro</code>
     */
    public PropositionalFunctionMacro getMacro() {
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
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental
        /*
         * PropositionalFunctionMacro macro = new PropositionalFunctionMacro(
         * this.macro); Map<Token, Term> paramMap = new HashMap<Token, Term>();
         * for (Token token : this.paramMap.keySet()) paramMap.put((Token)
         * token.deepCopy(), this.paramMap.get(token) .deepTermCopy());
         * 
         * try { return new PropositionalFunctionMacroInstance(macro, paramMap);
         * } catch (InvalidParametersException exc) { // This should never
         * happen! assert (false); throw new RuntimeException(
         * "Unexpected situation while copying function macro instance.", exc);
         * }
         */
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Term term : paramMap.values())
            variables.addAll(term.getArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Term term : paramMap.values())
            variables.addAll(term.getDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Term term : paramMap.values())
            variables.addAll(term.getPropositionalVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        Map<Token, Term> paramMap = new HashMap<Token, Term>(this.paramMap);
        return PropositionalFunctionMacroInstance.create(
                macro.negationNormalForm(), paramMap);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
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
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
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
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
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

        if (!((PropositionalFunctionMacroInstance) obj).macro.equals(macro))
            return false;
        if (!((PropositionalFunctionMacroInstance) obj).paramMap
                .equals(paramMap))
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
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
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
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap) {
        Map<Token, Term> convertedMap = new HashMap<Token, Term>();

        for (Token token : this.paramMap.keySet())
            convertedMap.put(token,
                    this.paramMap.get(token).substituteTerm(paramMap));

        try {
            return PropositionalFunctionMacroInstance.create(macro,
                    convertedMap);
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpected exception while converting PropositionalFunctionMacroInstance to caller scope.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualitiesTerm()
     */
    @Override
    public Formula removeArrayEqualities() {
        PropositionalFunctionMacro macro = this.macro.removeArrayEqualities();

        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet()) {
            paramMap2.put(token, paramMap.get(token)
                    .removeArrayEqualitiesTerm());
        }
        try {
            return PropositionalFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */

    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        PropositionalFunctionMacro macro = this.macro
                .arrayPropertiesToFiniteConjunctions(indexSet);

        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet()) {
            paramMap2.put(token, paramMap.get(token)
                    .arrayPropertiesToFiniteConjunctionsTerm(indexSet));
        }
        try {
            return PropositionalFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        PropositionalFunctionMacro macro = this.macro.simplify();

        Boolean simplification = macro.simplify(paramMap);
        if (simplification != null)
            return PropositionalConstant.create(simplification);

        try {
            return PropositionalFunctionMacroInstance.create(macro, paramMap);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        return macro.getBody().substituteFormula(paramMap).flatten();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
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
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Set<Formula> localConstraints = new HashSet<Formula>();
        PropositionalFunctionMacro macro = this.macro.removeArrayWrites(
                topLevelFormula, localConstraints, noDependenceVars);
        for (Formula localConstraint : localConstraints)
            constraints.add(localConstraint.substituteFormula(paramMap));

        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet()) {
            paramMap2.put(
                    token,
                    paramMap.get(token).removeArrayWritesTerm(topLevelFormula,
                            constraints, noDependenceVars));
        }

        try {
            return PropositionalFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        PropositionalFunctionMacro macro = this.macro
                .arrayReadsToUninterpretedFunctions(noDependenceVars);
        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        for (Token key : paramMap.keySet()) {
            Term term = paramMap.get(key);
            if (term instanceof ArrayRead)
                paramMap2.put(key, ((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars));
            else
                paramMap2
                        .put(key,
                                term.arrayReadsToUninterpretedFunctionsTerm(noDependenceVars));
        }
        try {
            return PropositionalFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return macro.getUninterpretedFunctions();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Formula substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions) {
        PropositionalFunctionMacro macro = this.macro
                .substituteUninterpretedFunction(substitutions);
        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet()) {
            paramMap2.put(token, paramMap.get(token)
                    .substituteUninterpretedFunctionTerm(substitutions));
        }
        try {
            return PropositionalFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
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
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {

        Set<Formula> localConstraints = new HashSet<Formula>();
        PropositionalFunctionMacro macro = this.macro.makeArrayReadsSimple(
                topLevelFormula, localConstraints, noDependenceVars);

        // TODO: does substituteFormula change the localConstraint object? i
        // hope not
        for (Formula localConstraint : localConstraints)
            constraints.add(localConstraint.substituteFormula(paramMap));

        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet()) {
            paramMap2.put(
                    token,
                    paramMap.get(token).makeArrayReadsSimpleTerm(
                            topLevelFormula, constraints, noDependenceVars));
        }
        try {
            return PropositionalFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }

    }

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
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */
    @Override
    public OrFormula transformToConsequentsForm() {
        throw new RuntimeException(
                "transformToConsequentsForm cannot be called on an PropositionalFunctionMacroInstance.\n"
                        + "PropositionalFunctionMacroInstance should be removed by now.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean,
     *      boolean)
     */
    @Override
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {
        throw new RuntimeException(
                "transformToConsequentsForm cannot be called on an PropositionalFunctionMacroInstance.\n"
                        + "PropositionalFunctionMacroInstance should be removed by now.");
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(SMTLibObject o) {
        return this.toString().compareTo(o.toString());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.List,
     *      java.util.Map)
     */
    @Override
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding, int partition) {
        throw new RuntimeException(
                "Macros should have been flattened before Tseitin encoding!");
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

        PropositionalFunctionMacro macro = this.macro
                .uninterpretedPredicatesToAuxiliaryVariables(topLeveFormula,
                        predicateInstances, instanceParameters,
                        noDependenceVars);
        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();

        for (Token token : paramMap.keySet()) {
            paramMap2.put(
                    token,
                    paramMap.get(token)
                            .uninterpretedPredicatesToAuxiliaryVariablesTerm(
                                    topLeveFormula, predicateInstances,
                                    instanceParameters, noDependenceVars));
        }
        try {
            return PropositionalFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
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

        PropositionalFunctionMacro macro = this.macro
                .uninterpretedFunctionsToAuxiliaryVariables(topLeveFormula,
                        functionInstances, instanceParameters, noDependenceVars);

        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet())
            paramMap2.put(
                    token,
                    paramMap.get(token)
                            .uninterpretedFunctionsToAuxiliaryVariablesTerm(
                                    topLeveFormula, functionInstances,
                                    instanceParameters, noDependenceVars));

        try {
            return PropositionalFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        throw new RuntimeException(
                "replaceEquivalences cannot be called on an PropositionalFunctionMacroInstance.\n"
                        + "PropositionalFunctionMacroInstance should be removed by now.");
    }

    @Override
    public Formula removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        throw new RuntimeException(
                "removeDomainITE cannot be called on an PropositionalFunctionMacroInstance.\n"
                        + "PropositionalFunctionMacroInstance should be removed by now.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public Formula uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars) {
        Map<Token, Term> newParamMap = new HashMap<Token, Term>();
        for (Token key : paramMap.keySet()) {
            newParamMap.put(key, paramMap.get(key)
                    .uninterpretedFunctionsBackToArrayReads(arrayVars));
        }
        PropositionalFunctionMacro newMacro = macro
                .uninterpretedFunctionsBackToArrayReads(arrayVars);
        try {
            return PropositionalFunctionMacroInstance.create(newMacro,
                    newParamMap);
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpected InvalidParametersException while back-substituting array reads.",
                    exc);
        }
    }

    @Override
    public Formula removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        throw new RuntimeException(
                "removeArrayITE cannot be called on an PropositionalFunctionMacroInstance.\n"
                        + "PropositionalFunctionMacroInstance should be removed by now.");
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
        throw new NotImplementedException();
    }

}
