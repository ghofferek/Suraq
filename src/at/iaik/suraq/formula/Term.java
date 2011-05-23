/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.List;

/**
 * This abstract class represents terms. Terms can be domain terms, array terms,
 * or "propositional terms". Strictly following the grammar, the latter would be
 * formulas, but treating them like terms eases handling of (in)equalities and
 * if-then-else constructs.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class Term {

    /**
     * Checks whether all terms in the given list are compatible for
     * (dis)equality operations.
     * 
     * @param termList
     *            the list of terms to check.
     * @return <code>true</code> if all terms can be compared by (dis)equality,
     *         <code>false</code> otherwise.
     */
    public static boolean checkTypeCompatibility(List<Term> termList) {

        if (termList.size() < 2) // 1 term always compatible.
            return true;

        Class<?> type = null;
        Class<?> domainTermClass;
        Class<?> arrayTermClass;
        Class<?> propositionalTermClass;
        try {

            domainTermClass = Class.forName("at.iaik.suraq.formula.DomainTerm");
            arrayTermClass = Class.forName("at.iaik.suraq.formula.ArrayTerm");
            propositionalTermClass = Class
                    .forName("at.iaik.suraq.formula.PropositionalTerm");
        } catch (ClassNotFoundException exc) {
            throw new RuntimeException(exc);
        }

        Term firstTerm = termList.get(0);

        if (domainTermClass.isInstance(firstTerm))
            type = domainTermClass;

        if (arrayTermClass.isInstance(firstTerm))
            type = arrayTermClass;

        if (propositionalTermClass.isInstance(firstTerm))
            type = propositionalTermClass;

        for (Term term : termList.subList(1, termList.size())) {
            if (!type.isInstance(term))
                return false;
        }
        return true;

    }
}
