/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Serializable;
import java.io.Writer;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.HashTagContainer;

/**
 * This abstract class represents terms. Terms can be domain terms, array terms,
 * or "propositional terms". Strictly following the grammar, the latter would be
 * formulas, but treating them like terms eases handling of (in)equalities and
 * if-then-else constructs.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class Term implements Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = -5654824580231056142L;

    public static final Class<?> domainTermClass = (DomainVariable.create(""))
            .getClass().getSuperclass();
    public static final Class<?> arrayTermClass = (ArrayVariable.create(""))
            .getClass().getSuperclass();
    public static final Class<?> propositionalTermClass = (PropositionalVariable
            .create("")).getClass().getSuperclass();

    public final static int GLOBAL_PARTITION = -1;

    /**
     * The assert-partitions
     */
    protected int assertPartition = Term.GLOBAL_PARTITION;

    /**
     * Checks whether all terms in the given list are compatible for
     * (dis)equality operations. If so, the type is returned.
     * 
     * @param terms
     *            the list of terms to check.
     * @return the type of the terms in <code>termList</code> or
     *         <code>null</code> if there are multiple incompatible types.
     */
    public static Class<?> checkTypeCompatibility(
            Collection<? extends Term> terms) {

        if (terms.size() < 1)
            return null;

        Class<?> type = null;

        Term firstTerm = terms.iterator().next();

        if (Term.domainTermClass.isInstance(firstTerm))
            type = Term.domainTermClass;

        if (Term.arrayTermClass.isInstance(firstTerm))
            type = Term.arrayTermClass;

        if (Term.propositionalTermClass.isInstance(firstTerm))
            type = Term.propositionalTermClass;

        boolean allOk = true;
        for (Term term : terms) {
            if (!type.isInstance(term))
                allOk = false;
        }
        if (allOk)
            return type;
        else
            return null;

    }

    /**
     * Returns the type of this term.
     * 
     * @return the type of this term.
     */
    public abstract SExpression getType();

    /**
     * Returns a deep copy of this term.
     * 
     * @return a deep copy of this term.
     */
    public abstract Term deepTermCopy();

    /**
     * Returns a set of all array variables used in this term.
     * 
     * @return a set of array variables used in this term.
     */
    public abstract Set<ArrayVariable> getArrayVariables();

    /**
     * Returns a set of all domain variables used in this term.
     * 
     * @return a set of domain variables used in this term.
     */
    public abstract Set<DomainVariable> getDomainVariables();

    /**
     * Returns a set of all propositional variables used in this term.
     * 
     * @return a set of propositional variables used in this term.
     */
    public abstract Set<PropositionalVariable> getPropositionalVariables();

    /**
     * Returns a set of all function macro names used in this term.
     * 
     * @return a set of function macro names used in this term.
     */
    public abstract Set<String> getFunctionMacroNames();

    /**
     * Returns a set of all function macros used in this term.
     * 
     * @return a set of all function macros used in this term.
     */
    public abstract Set<FunctionMacro> getFunctionMacros();

    /**
     * Returns a set of all uninterpreted function names used in this formula.
     * 
     * @return a set of uninterpreted function names used in this formula.
     */
    public abstract Set<String> getUninterpretedFunctionNames();

    /**
     * Returns a new term that is a version of this term, with the substitutions
     * given by the given map applied. E.g., the local term of a function
     * macro's body is converted to the (more) global term of the macro's
     * instance. Terms which are not found in the map are returned unchanged.
     * 
     * @param paramMap
     *            the map to convert local terms to the caller's scope
     * @return a (new) term, converted according to the given map.
     */
    public abstract Term substituteTerm(Map<Token, ? extends Term> paramMap);

    /**
     * Computes the index set of this term. I.e., if it is an array read, its
     * index term is returned (as a singleton). For other term types, an empty
     * set is returned.
     * 
     * @return the index set.
     * @throws SuraqException
     *             if the term is an array write expressions, or computation
     *             otherwise fails.
     */
    public abstract Set<DomainTerm> getIndexSet() throws SuraqException;

    /**
     * Converts this term into an s-expression compatible with SMTLIBv2. Only
     * the term itself is converted. No variable/function/macro declarations are
     * included.
     * 
     * @return this term as an SMTLIBv2 s-expression.
     */
    public abstract SExpression toSmtlibV2();

    /**
     * Reduces all array properties in this formula to finite conjunctions over
     * the given index set. The index set must already include the special
     * variable lambda.
     * 
     * @param indexSet
     *            the index set.
     */
    public abstract Term arrayPropertiesToFiniteConjunctionsTerm(
            Set<DomainTerm> indexSet);

    /**
     * Replaces all array equalities in this formula by equivalent array
     * properties.
     */
    public abstract Term removeArrayEqualitiesTerm();

    /**
     * Recursively replaces all array writes by applying the write axiom.
     * 
     * @param topLevelFormula
     *            The top-level formula on which the recursion started. (Needed
     *            to determine fresh variable names.)
     * @param constraints
     *            A set to which constraints coming from write-axiom application
     *            will be added. * @param noDependenceVars A set of variables on
     *            which the controller may not depend. Newly created variables
     *            on which the controller may not depend are added to this set
     *            during recursion.
     */
    public abstract Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars);

    /**
     * Replaces all array-read expressions with uninterpreted function instances
     * of the same name.
     * 
     * @param noDependenceVars
     *            the variables on which the controller may not depend. New such
     *            variables are added to this set during recursion.
     * 
     */
    public abstract Term arrayReadsToUninterpretedFunctionsTerm(
            Set<Token> noDependenceVars);

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    public abstract Set<UninterpretedFunction> getUninterpretedFunctions();

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    // public abstract Term substituteUninterpretedFunctionTerm(Token
    // oldFunction,
    // UninterpretedFunction newFunction);

    // chillebold:
    public abstract Term substituteUninterpretedFunctionTerm(
            Map<Token, UninterpretedFunction> substitutions);

    /**
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.toSmtlibV2().toString();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    public abstract Term flatten();

    /**
     * @param topLevelFormula
     *            TODO
     * @param noDependenceVars
     *            TODO
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(Formula,
     *      at.iaik.suraq.smtlib.formula.Formula, Set)
     */
    public abstract Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars);

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    public abstract Set<Integer> getPartitionsFromSymbols();

    /**
     * Replaces instances of uninterpreted predicates in formula with auxiliary
     * boolean variables.
     * 
     * @param topLeveFormula
     *            the top level formula (for finding fresh variable names).
     * 
     * @param predicateInstances
     *            map containing mapping from predicate names to boolean
     *            auxiliary variables.
     * 
     * @param instanceParameters
     *            map containing mapping from boolean auxiliary variables to
     *            predicate instance parameters.
     * 
     * @return a new formula with uninterpreted predicates replaced by boolean
     *         auxiliary variables.
     */

    public abstract Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars);

    /**
     * Replaces instances of uninterpreted functions in formula with auxiliary
     * variables.
     * 
     * 
     * @param topLeveFormula
     *            the top level formula (for finding fresh variable names).
     * 
     * @param functionInstances
     *            map containing mapping from function names to auxiliary
     *            variables.
     * 
     * @param instanceParameters
     *            map containing mapping from auxiliary variables to function
     *            instance parameters.
     * 
     * @return a new formula with uninterpreted predicates replaced by auxiliary
     *         variables.
     */
    public abstract Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars);

    /**
     * @param arrayVars
     * @return a term where matching uninterpreted function instances are
     *         replaced by array reads.
     */
    public abstract Term uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars);

    /**
     * A new <code>Term</code> where DomainITEs have been replaced with new
     * variables.
     * 
     * @param topLevelFormula
     * @param noDependenceVars
     * @param andPreList
     * @return
     */
    public abstract Term removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList);

    /**
     * @param topLevelFormula
     * @param noDependenceVars
     * @param constraints
     * @return
     */
    public abstract Term removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints);

    /**
     * @param writer
     * @param tagContainer
     * @param handleThisWithTagContainer
     */
    public abstract void writeOut(BufferedWriter writer,
            HashTagContainer tagContainer) throws IOException;

    /**
     * Writes the term to the given writer. Essentially, this should write the
     * same thing as would be produced by <code>toString</code>.
     * 
     * @param writer
     * @throws IOException
     */
    public abstract void writeTo(Writer writer) throws IOException;

}
