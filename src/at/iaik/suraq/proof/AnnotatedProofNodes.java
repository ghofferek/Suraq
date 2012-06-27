/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.util.HashMap;
import java.util.Map;

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

    private Map<Formula, AnnotatedProofNode> map = new HashMap<Formula, AnnotatedProofNode>();

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
     * @return a node with the given consequent or <code>null</code> if such a
     *         node does not exist.
     */
    public AnnotatedProofNode getNodeWithConsequent(Formula consequent) {
        return map.get(consequent.transformToConsequentsForm());
    }

    public void add(AnnotatedProofNode node) {
        assert (node != null);
        assert (node.getConsequent() != null);
        assert (node.getConsequent().getConsequent() != null);
        map.put(node.getConsequent().getConsequent()
                .transformToConsequentsForm(), node);
    }
}
