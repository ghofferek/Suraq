/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.Collection;
import java.util.Set;

import at.iaik.suraq.sexp.SExpression;

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

}
