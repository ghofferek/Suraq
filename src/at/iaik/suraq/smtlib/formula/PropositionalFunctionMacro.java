/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * This class represents a (Boolean) function macro. It represents the
 * "define-fun" part of the input. Do not confuse it with
 * <code>PropositionalFunctionMacroInstance</code> which is an actual instance
 * of a macro.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class PropositionalFunctionMacro extends FunctionMacro {

    /**
     * The body of this macro.
     */
    private final Formula body;

    /**
     * Constructs a new <code>PropositionalFunctionMacro</code> with the given
     * values.
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
    public PropositionalFunctionMacro(Token name, List<Token> parameters,
            Map<Token, SExpression> paramMap, Formula body)
            throws InvalidParametersException {
        super(name, parameters, paramMap);
        this.body = body;
    }

    /**
     * Constructs a new <code>PropositionalFunctionMacro</code>, which is a deep
     * copy of the given one
     * 
     * @param macro
     *            the macro to (deep) copy.
     */
    public PropositionalFunctionMacro(PropositionalFunctionMacro macro) {
        super(macro);
        this.body = macro.body.deepFormulaCopy();
    }

    /**
     * Returns the function body of this macro.
     * 
     * @return the <code>body</code>
     */
    public Formula getBody() {
        return body;
    }

    /**
     * Creates a new macro, which is the same as this one, but in NNF.
     * 
     * @return a copy of this macro in NNF.
     * @throws SuraqException
     *             if conversion to NNF fails (e.g. due to invalid array
     *             properties)
     */
    public PropositionalFunctionMacro negationNormalForm()
            throws SuraqException {
        assert (!name.toString().endsWith("NNF"));

        Token nnfName = Token.generate(name.toString() + "NNF");
        Map<Token, SExpression> nnfParamMap = new HashMap<Token, SExpression>(
                paramMap);
        List<Token> nnfParameters = new ArrayList<Token>(parameters);

        Formula nnfBody = body.negationNormalForm();

        return new PropositionalFunctionMacro(nnfName, nnfParameters,
                nnfParamMap, nnfBody);
    }

    /**
     * Creates a macro with negated body, put in NNF.
     * 
     * @return a macro with a negated body, put in NNF.
     * @throws SuraqException
     */
    public PropositionalFunctionMacro negatedMacro() throws SuraqException {
        Token negatedName = Token.generate(name.toString() + "Negated");
        Map<Token, SExpression> negatedParamMap = new HashMap<Token, SExpression>(
                paramMap);
        List<Token> negatedParameters = new ArrayList<Token>(parameters);

        Formula negatedBody = (NotFormula.create(body)).negationNormalForm();

        return new PropositionalFunctionMacro(negatedName, negatedParameters,
                negatedParamMap, negatedBody);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof PropositionalFunctionMacro))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        PropositionalFunctionMacro other = (PropositionalFunctionMacro) obj;
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
                + paramMap.hashCode() * 31 ^ body.hashCode();
    }

    /**
     * Removes array equalities from the body of the macro.
     */
    @Override
    public PropositionalFunctionMacro removeArrayEqualities() {
        Formula body = this.body;
        if (body instanceof ArrayEq)
            body = ((ArrayEq) body).toArrayProperties();
        else
            body = body.removeArrayEqualities();

        try {
            return new PropositionalFunctionMacro(name, parameters, paramMap, body);
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
    public PropositionalFunctionMacro arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        Formula body = this.body;
        if (body instanceof ArrayProperty)
            body = ((ArrayProperty) body).toFiniteConjunction(indexSet);
        else
            body = body.arrayPropertiesToFiniteConjunctions(indexSet);

        try {
            return new PropositionalFunctionMacro(name, parameters, paramMap, body);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * Simplifies the body of the macro.
     */
    public PropositionalFunctionMacro simplify() {
        Formula body = this.body.simplify();
        try {
            return new PropositionalFunctionMacro(name, parameters, paramMap, body);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * Simplifies the body of the macro after substituting local variables
     * according to the given map. If the result is a constant, it is returned
     * as a <code>Boolean</code>. Otherwise, <code>null</code> is returned.
     * 
     * @param paramMap
     *            the map for substituting local variables.
     * @return <code>null</code>, if simplifcation does not yield a constant.
     *         The constant as a <code>Boolean</code> otherwise.
     */
    public Boolean simplify(Map<Token, Term> paramMap) {

        Formula bodyCopy = body.deepFormulaCopy();

        bodyCopy = bodyCopy.substituteFormula(paramMap);
        bodyCopy = bodyCopy.simplify();

        if (bodyCopy instanceof PropositionalConstant)
            return ((PropositionalConstant) bodyCopy).getValue();

        return null;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.FunctionMacro#getType()
     */
    @Override
    public SExpression getType() {
        return SExpressionConstants.BOOL_TYPE;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.EqualityFormula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */

    public PropositionalFunctionMacro removeArrayWrites(
            Formula topLevelFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        Formula body = this.body.removeArrayWrites(topLevelFormula,
                constraints, noDependenceVars);

        try {
            return new PropositionalFunctionMacro(name, parameters, paramMap,
                    body);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * Replaces array-read expression with uninterpreted function instances
     */
    public PropositionalFunctionMacro arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        Formula body = this.body
                .arrayReadsToUninterpretedFunctions(noDependenceVars);
        try {
            return new PropositionalFunctionMacro(name, parameters, paramMap,
                    body);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        return body.getUninterpretedFunctions();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.FunctionMacro#getBodyExpression()
     */
    @Override
    public SExpression getBodyExpression() {
        return body.toSmtlibV2();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    public PropositionalFunctionMacro substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {

        Formula body = this.body.substituteUninterpretedFunction(oldFunction,
                newFunction);
        try {
            return new PropositionalFunctionMacro(name, parameters, paramMap,
                    body);
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
    public PropositionalFunctionMacro makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        Formula body = this.body.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        try {
            return new PropositionalFunctionMacro(name, parameters, paramMap,
                    body);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*public PropositionalFunctionMacro uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {

        Formula newBody = body.uninterpretedPredicatesToAuxiliaryVariables(
                topLeveFormula, constraints, noDependenceVars);
        try {
            return new PropositionalFunctionMacro(name, parameters, paramMap,
                    newBody);
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpectedly unable to create PropositionalFunctionMacro.",
                    exc);
        }

    }*/

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
    public PropositionalFunctionMacro uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        Formula body = this.body;
        if (body instanceof UninterpretedPredicateInstance)
            body = ((UninterpretedPredicateInstance) body)
                    .applyReplaceUninterpretedPredicates(topLeveFormula,
                            predicateInstances, instanceParameters,
                            noDependenceVars);
        else
            body = body.uninterpretedPredicatesToAuxiliaryVariables(
                    topLeveFormula, predicateInstances, instanceParameters,
                    noDependenceVars);

        try {
            return new PropositionalFunctionMacro(name, parameters, paramMap,
                    body);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
    
    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    public PropositionalFunctionMacro uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        Formula body = this.body.uninterpretedFunctionsToAuxiliaryVariables(
                topLeveFormula, functionInstances, instanceParameters,
                noDependenceVars);

        try {
            return new PropositionalFunctionMacro(name, parameters, paramMap,
                    body);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
}
