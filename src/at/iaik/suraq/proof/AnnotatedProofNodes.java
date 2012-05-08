/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.util.HashSet;
import java.util.Iterator;

import at.iaik.suraq.smtlib.formula.Formula;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class AnnotatedProofNodes extends HashSet<AnnotatedProofNode> {

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
        Iterator<AnnotatedProofNode> iterator = this.iterator();
        while (iterator.hasNext()) {
            AnnotatedProofNode currentNode = iterator.next();
            if (currentNode.hasConsequent(consequent))
                return currentNode;
        }
        return null;
    }
}
