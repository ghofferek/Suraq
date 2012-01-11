/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * This abstract class represents terms. Terms can be domain terms, array terms,
 * or "propositional terms". Strictly following the grammar, the latter would be
 * formulas, but treating them like terms eases handling of (in)equalities and
 * if-then-else constructs.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class Term {

    public static final Class<?> domainTermClass = (new DomainVariable(""))
            .getClass().getSuperclass();
    public static final Class<?> arrayTermClass = (new ArrayVariable(""))
            .getClass().getSuperclass();
    public static final Class<?> propositionalTermClass = (new PropositionalVariable(
            "")).getClass().getSuperclass();

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
    public abstract Term substituteTerm(Map<Token, Term> paramMap);

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
    public abstract void arrayPropertiesToFiniteConjunctions(
            Set<DomainTerm> indexSet);

    /**
     * Replaces all array equalities in this formula by equivalent array
     * properties.
     */
    public abstract void removeArrayEqualities();

    /**
     * Recursively replaces all array writes by applying the write axiom.
     * 
     * @param topLevelFormula
     *            The top-level formula on which the recursion started. (Needed
     *            to determine fresh variable names.)
     * @param constraints
     *            A set to which constraints coming from write-axiom application
     *            will be added.
     */
    public abstract void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints);

}
