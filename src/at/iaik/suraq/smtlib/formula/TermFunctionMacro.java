/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.InvalidParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TermFunctionMacro extends FunctionMacro {

    /**
     * The body of this macro.
     */
    private Term body;

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
    public TermFunctionMacro(Token name, List<Token> parameters,
            Map<Token, SExpression> paramMap, Term body)
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
    public TermFunctionMacro(TermFunctionMacro macro) {
        super(macro);
        this.body = macro.body.deepTermCopy();
    }

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
            return new TermFunctionMacro(name, parameters, paramMap, body.removeArrayEqualitiesTerm());
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.FunctionMacro#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public FunctionMacro arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        try {
            return new TermFunctionMacro(name, parameters, paramMap, body.arrayPropertiesToFiniteConjunctionsTerm(indexSet));
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
        body.removeArrayWritesTerm(topLevelFormula, constraints, noDependenceVars);
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
            return new TermFunctionMacro(name, parameters, paramMap, body);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
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
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    public FunctionMacro substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        try {
            Term tmp = body.substituteUninterpretedFunctionTerm(oldFunction,
                    newFunction);
            return new TermFunctionMacro(name, parameters, paramMap, tmp);
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
    /*public TermFunctionMacro uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {

        Term newBody = body.uninterpretedPredicatesToAuxiliaryVariables(
                topLeveFormula, constraints, noDependenceVars);
        try {
            return new TermFunctionMacro(name, parameters, paramMap, newBody);
        } catch (InvalidParametersException exc) {
            throw new RuntimeException(
                    "Unexpectedly unable to create TermFunctionMacro.", exc);
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
    public FunctionMacro uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        Term tmp = body.uninterpretedPredicatesToAuxiliaryVariablesTerm(
                topLeveFormula, predicateInstances, instanceParameters,
                noDependenceVars);

        try {
            return new TermFunctionMacro(name, parameters, paramMap, tmp);
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
            return new TermFunctionMacro(name, parameters, paramMap, tmp);
        } catch (InvalidParametersException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }
}
