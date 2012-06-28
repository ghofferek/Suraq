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
public class AnnotatedProofNodes {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

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
     * @return a node with the given consequent or <code>null</code> if such a
     *         node does not exist.
     */
    public AnnotatedProofNode getNodeWithConsequent(Formula consequent,
            Set<Formula> hypotheses) {
        Map<Set<Formula>, AnnotatedProofNode> currentMap = map.get(consequent
                .transformToConsequentsForm());
        AnnotatedProofNode result = currentMap.get(hypotheses);
        return result;
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
