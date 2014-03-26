/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TermFunctionMacro extends FunctionMacro {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;
    /**
     * The body of this macro.
     */
    private final Term body;

    /**
     * Constructs a new <code>TermFunctionMacro</code> with the given values.
     * 
     * @param name
     *            the name of this macro.
     * @param a
     *            list of parameters
     * @param paramMap
     *            the map from parameters to types.
     * @param body
     *            the actual body.
     * @throws InvalidParametersException
     *             if the size of the parameter list and the type map do not
     *             match.
     */
    private TermFunctionMacro(Token name, List<Token> parameters,
            Map<Token, SExpression> paramMap, Term body)
            throws InvalidParametersException {
        super(name, parameters, paramMap);
        this.body = body;
    }

    public static TermFunctionMacro create(Token name, List<Token> parameters,
            Map<Token, SExpression> paramMap, Term body)
            throws InvalidParametersException {
        return (TermFunctionMacro) FormulaCache.functionMacro
                .put(new TermFunctionMacro(name, parameters, paramMap, body));
    }

    /**
     * Constructs a new <code>PropositionalFunctionMacro</code>, which is a deep
     * copy of the given one
     * 
     * @param macro
     *            the macro to (deep) copy.
     */
    /*
     * public TermFunctionMacro(TermFunctionMacro macro) { super(macro);
     * this.body = macro.body.deepTermCopy(); }
     */

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof TermFunctionMacro))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        TermFunctionMacro other = (TermFunctionMacro) obj;
        if (!other.name.equals(name))
            return false;
        if (!other.parameters.equals(parameters))
            return false;
        if (!other.paramMap.equals(paramMap))
            return false;
        if (!other.body.equals(body))
            return false;
        return true;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return name.hashCode() * 31 * 31 * 31 + parameters.hashCode() * 31 * 31
                + paramMap.hashCode() * 31 + body.hashCode();
    }

    /**
     * Returns the function body of this macro.
     * 
     * @return the <code>body</code>
     */
    public Term getBody() {
        return body;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.FunctionMacro#removeArrayEqualities()
     */
    @Override
    public FunctionMacro removeArrayEqualities() {
        try {
            return TermFunctionMacro.create(name, parameters, paramMap,
                    body.removeArrayEqualitiesTerm());
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.FunctionMacro#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public FunctionMacro arrayPropertiesToFiniteConjunctions(
            Set<DomainTerm> indexSet) {
        try {
            return TermFunctionMacro.create(name, parameters, paramMap,
                    body.arrayPropertiesToFiniteConjunctionsTerm(indexSet));
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * Returns the type of the term of this macro's body.
     * 
     * @return the type of the term of this macro's body.
     */
    @Override
    public SExpression getType() {
        return body.getType();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.EqualityFormula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    public Set<Formula> removeArrayWrites(Formula topLevelFormula,
            Set<Token> noDependenceVars) {
        Set<Formula> constraints = new HashSet<Formula>();
        body.removeArrayWritesTerm(topLevelFormula, constraints,
                noDependenceVars);
        return constraints;
    }

    /**
     * Replaces array-read expressions with uninterpreted function instances
     */
    public FunctionMacro arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        Term body = this.body
                .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);
        try {
            return TermFunctionMacro.create(name, parameters, paramMap, body);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        body.getUninterpretedFunctions(result, done);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.FunctionMacro#getBodyExpression()
     */
    @Override
    public SExpression getBodyExpression() {
        return body.toSmtlibV2();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public FunctionMacro substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null) {
            assert (done.get(this) instanceof FunctionMacro);
            return (FunctionMacro) done.get(this);
        }

        try {
            Term tmp = body
                    .substituteUninterpretedFunction(substitutions, done);
            FunctionMacro result = TermFunctionMacro.create(name, parameters,
                    paramMap, tmp);
            done.put(this, result);
            return result;
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @param topLevelFormula
     * @param noDependenceVars
     * @return
     */
    public Set<Formula> makeArrayReadsSimple(Formula topLevelFormula,
            Set<Token> noDependenceVars) {
        Set<Formula> constraints = new HashSet<Formula>();
        body.makeArrayReadsSimpleTerm(topLevelFormula, constraints,
                noDependenceVars);
        return constraints;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * public TermFunctionMacro uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) {
     * 
     * Term newBody = body.uninterpretedPredicatesToAuxiliaryVariables(
     * topLeveFormula, constraints, noDependenceVars); try { return new
     * TermFunctionMacro(name, parameters, paramMap, newBody); } catch
     * (InvalidParametersException exc) { throw new RuntimeException(
     * "Unexpectedly unable to create TermFunctionMacro.", exc); }
     * 
     * }
     */

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getAssertPartition() {
        return body.getPartitionsFromSymbols();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    public FunctionMacro uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        Term tmp = body.uninterpretedPredicatesToAuxiliaryVariablesTerm(
                topLeveFormula, predicateInstances, instanceParameters,
                noDependenceVars);

        try {
            return TermFunctionMacro.create(name, parameters, paramMap, tmp);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    public FunctionMacro uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        Term tmp = body.uninterpretedFunctionsToAuxiliaryVariablesTerm(
                topLeveFormula, functionInstances, instanceParameters,
                noDependenceVars);

        try {
            return TermFunctionMacro.create(name, parameters, paramMap, tmp);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @param arrayVars
     * @return
     */
    @Override
    public TermFunctionMacro uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars, Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null)
            return (TermFunctionMacro) done.get(this);
        Term newBody = (Term) body.uninterpretedFunctionsBackToArrayReads(
                arrayVars, done);
        try {
            TermFunctionMacro result = TermFunctionMacro.create(name,
                    parameters, paramMap, newBody);
            done.put(this, result);
            return result;
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpected InvalidParametersException while back-substituting array reads.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getPartitionsFromSymbols()
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getArrayVariables(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getDomainVariables(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getDomainVariables(Set<DomainVariable> result,
            Set<SMTLibObject> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getPropositionalVariables(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getPropositionalVariables(Set<PropositionalVariable> result,
            Set<SMTLibObject> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getUninterpretedFunctionNames(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getFunctionMacroNames(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        result.add(this.name.toString());
    }

    /**
     * @see at.iaik.suraq.smtlib.SMTLibObject#getFunctionMacros(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getFunctionMacros(Set<FunctionMacro> result,
            Set<SMTLibObject> done) {
        result.add(this);
    }
}
