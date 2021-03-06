/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.smtlib.formula.Formula;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public final class AnnotatedProofNodes {

    /**
     * 
     */
    //private static final long serialVersionUID = 1L;

    private Map<Formula, Map<Set<Formula>, AnnotatedProofNode>> map = new HashMap<Formula, Map<Set<Formula>, AnnotatedProofNode>>();

    /**
     * Constructs a new <code>AnnotatedProofNodes</code> set.
     */
    public AnnotatedProofNodes() {
        super();
    }

    /**
     * Returns a node that has the given consequent. Uses the
     * <code>equals</code> method of formulas to determine equality.
     * 
     * @param consequent
     *            the consequent to look for
     * @param hypotheses
     *            the set of hypotheses the searched node should have
     * @param obsoleteLiterals
     *            a call-by-reference parameter, via which the new obsolete
     *            literals (if any) will be returned. Must be an empty set at
     *            call time!
     * @return a node with the given consequent or <code>null</code> if such a
     *         node does not exist.
     */
    public AnnotatedProofNode getNodeWithConsequent(Formula consequent,
            Set<Formula> hypotheses, Set<Formula> obsoleteLiterals) {
        assert (obsoleteLiterals.isEmpty());
        Map<Set<Formula>, AnnotatedProofNode> currentMap = map.get(consequent
                .transformToConsequentsForm());

        if (currentMap == null)
            return null;

        // TODO Instead of returning a node with matching hypotheses, or
        // a matching subset, one could search for the smallest subset here.
        // This would decrease overall proof size.

        AnnotatedProofNode result = currentMap.get(hypotheses);
        if (result == null) {
            for (AnnotatedProofNode potentialResult : currentMap.values()) {
                if (hypotheses.containsAll(potentialResult.getHypotheses())) {
                    obsoleteLiterals.addAll(hypotheses);
                    obsoleteLiterals.removeAll(potentialResult.getHypotheses());
                    return potentialResult;
                }
            }
        }
        return result;
    }

    /**
     * Returns an annotated node with a consequent that has the given id. If no
     * such node exists, <code>null</code> is returned. This method iterated
     * through the internal map(s) and is thus very inefficient!
     * 
     * @param id
     * @return an annotated node whose consequent has the given <code>id</code>,
     *         or <code>null</code> if no such node exists.
     */
    public AnnotatedProofNode getNodeWithId(int id) {
        for (Map<Set<Formula>, AnnotatedProofNode> currentMap : map.values()) {
            for (AnnotatedProofNode node : currentMap.values())
                if (node.getConsequent().getID() == id)
                    return node;
        }
        return null;
    }

    public void add(AnnotatedProofNode node) {
        assert (node != null);
        assert (node.getConsequent() != null);
        assert (node.getConsequent().getConsequent() != null);
        Formula formula = node.getConsequent().getConsequent()
                .transformToConsequentsForm();

        Map<Set<Formula>, AnnotatedProofNode> currentMap = map.get(formula);
        if (currentMap == null) {
            currentMap = new HashMap<Set<Formula>, AnnotatedProofNode>();
            map.put(formula, currentMap);
        }
        currentMap.put(node.getHypotheses(), node);

    }
}
