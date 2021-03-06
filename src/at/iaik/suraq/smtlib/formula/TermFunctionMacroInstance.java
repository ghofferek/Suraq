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
    private final ImmutableHashMap<Token, Term> paramMap;

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
    private TermFunctionMacroInstance(TermFunctionMacro macro,
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
        this.paramMap = new ImmutableHashMap<Token, Term>(paramMap);
    }

    public static TermFunctionMacroInstance create(TermFunctionMacro macro,
            Map<Token, Term> paramMap) throws InvalidParametersException {
        return (TermFunctionMacroInstance) FormulaCache.domainTerm
                .put(new TermFunctionMacroInstance(macro, paramMap));
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
        return this; // experimental
        /*
         * TermFunctionMacro macro = new TermFunctionMacro(this.macro);
         * Map<Token, Term> paramMap = new HashMap<Token, Term>(); for (Token
         * token : this.paramMap.keySet()) paramMap.put((Token)
         * token.deepCopy(), this.paramMap.get(token) .deepTermCopy());
         * 
         * try { return new TermFunctionMacroInstance(macro, paramMap); } catch
         * (InvalidParametersException exc) { // This should never happen!
         * assert (false); throw new RuntimeException(
         * "Unexpected situation while copying function macro instance.", exc);
         * }
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
        for (Term term : paramMap.values())
            term.getArrayVariables(result, done);
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
        for (Term term : paramMap.values())
            term.getDomainVariables(result, done);
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
        for (Term term : paramMap.values())
            term.getPropositionalVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : paramMap.values())
            term.getFunctionMacroNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public void getFunctionMacros(Set<FunctionMacro> result,
            Set<SMTLibObject> done) {
        result.add(macro);
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
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : paramMap.values())
            term.getUninterpretedFunctionNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getUninterpretedFunctions(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : paramMap.values())
            term.getUninterpretedFunctions(result, done);
        done.add(this);

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
        Map<Token, Term> convertedMap = new HashMap<Token, Term>();

        for (Token token : this.paramMap.keySet())
            convertedMap.put(
                    token,
                    this.paramMap.get(token).substituteTerm(paramMap,
                            new HashMap<SMTLibObject, SMTLibObject>()));

        try {
            Term result = new TermFunctionMacroInstance(macro, convertedMap);
            assert (result != null);
            done.put(this, result);
            return result;
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
            result.add((DomainTerm) term.substituteTerm(paramMap,
                    new HashMap<SMTLibObject, SMTLibObject>()));
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
            return TermFunctionMacroInstance.create(macro, paramMap);
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
            return TermFunctionMacroInstance.create(macro, paramMap);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        // FIXME: this cannot work:

        throw new RuntimeException("Cannot work");
        // Set<Formula> localConstraints = macro.removeArrayWrites(
        // topLevelFormula, noDependenceVars);
        // for (Formula localConstraint : localConstraints)
        // constraints.add(localConstraint.substituteFormula(paramMap));
        //
        // Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        // for (Token key : paramMap.keySet()) {
        // // for (Term term : paramMap.values())
        // paramMap2.put(
        // key,
        // paramMap.get(key).removeArrayWritesTerm(topLevelFormula,
        // constraints, noDependenceVars));
        // }
        // try {
        // return new TermFunctionMacroInstance(macro, paramMap2);
        // } catch (InvalidParametersException e) {
        // e.printStackTrace();
        // throw new RuntimeException(e);
        // }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(
            Set<Token> noDependenceVars) {
        TermFunctionMacro macro = (TermFunctionMacro) this.macro
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
            return TermFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public TermFunctionMacroInstance substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null) {
            assert (done.get(this) instanceof TermFunctionMacroInstance);
            return (TermFunctionMacroInstance) done.get(this);
        }
        TermFunctionMacro macro = (TermFunctionMacro) this.macro
                .substituteUninterpretedFunction(substitutions, done);

        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet())
            paramMap2.put(token, this.paramMap.get(token)
                    .substituteUninterpretedFunction(substitutions, done));

        try {
            TermFunctionMacroInstance result = TermFunctionMacroInstance
                    .create(macro, paramMap2);
            done.put(this, result);
            return result;
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
        return macro
                .getBody()
                .substituteTerm(paramMap,
                        new HashMap<SMTLibObject, SMTLibObject>()).flatten();
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
        for (Formula localConstraint : localConstraints) {
            Map<SMTLibObject, SMTLibObject> done = new HashMap<SMTLibObject, SMTLibObject>();
            constraints.add(localConstraint.substituteFormula(paramMap, done));
        }
        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet())
            paramMap2.put(
                    token,
                    paramMap.get(token).makeArrayReadsSimpleTerm(
                            topLevelFormula, constraints, noDependenceVars));

        try {
            return TermFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public DomainTerm uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { Set<Formula> localConstraints = new
     * HashSet<Formula>(); TermFunctionMacro newMacro = macro
     * .uninterpretedPredicatesToAuxiliaryVariables(topLeveFormula,
     * localConstraints, noDependenceVars); for (Formula localConstraint :
     * localConstraints)
     * constraints.add(localConstraint.substituteFormula(paramMap));
     * 
     * Map<Token, Term> newParamMap = new HashMap<Token, Term>(); for (Token
     * token : paramMap.keySet()) newParamMap.put( token, paramMap.get(token)
     * .uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars)); try { return new
     * TermFunctionMacroInstance(newMacro, newParamMap); } catch
     * (InvalidParametersException exc) { throw new RuntimeException(
     * "Unexpectedly unable to create TermFunctionMacroInstance.", exc); } }
     */

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
    @Override
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        TermFunctionMacro macro = (TermFunctionMacro) this.macro
                .uninterpretedPredicatesToAuxiliaryVariables(topLeveFormula,
                        predicateInstances, instanceParameters,
                        noDependenceVars);

        Map<Token, Term> paramMap2 = new HashMap<Token, Term>();
        for (Token token : paramMap.keySet())
            paramMap2.put(
                    token,
                    paramMap.get(token)
                            .uninterpretedPredicatesToAuxiliaryVariablesTerm(
                                    topLeveFormula, predicateInstances,
                                    instanceParameters, noDependenceVars));

        try {
            return TermFunctionMacroInstance.create(macro, paramMap2);
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
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        TermFunctionMacro macro = (TermFunctionMacro) this.macro
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
            return TermFunctionMacroInstance.create(macro, paramMap2);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public DomainTerm uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars, Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null)
            return (DomainTerm) done.get(this);

        Map<Token, Term> newParamMap = new HashMap<Token, Term>();
        for (Token key : paramMap.keySet()) {
            newParamMap.put(key, (Term) paramMap.get(key)
                    .uninterpretedFunctionsBackToArrayReads(arrayVars, done));
        }
        TermFunctionMacro newMacro = macro
                .uninterpretedFunctionsBackToArrayReads(arrayVars, done);
        try {
            DomainTerm result = TermFunctionMacroInstance.create(newMacro,
                    newParamMap);
            done.put(this, result);
            return result;
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpected InvalidParametersException while back-substituting array reads.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#removeDomainITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.List)
     */
    @Override
    public DomainTerm removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        throw new RuntimeException(
                "Macros should be flattened before removing DomainITEs.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public DomainTerm removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        throw new RuntimeException(
                "Macros should be flattened before removing ArrayITEs.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#writeOut(java.io.BufferedWriter,
     *      at.iaik.suraq.util.HashTagContainer, boolean)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContaine)
            throws IOException {
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
