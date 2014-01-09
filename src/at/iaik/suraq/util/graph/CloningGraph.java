/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util.graph;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.util.Copyable;

/**
 * This class does exactly the same as the superclass, except for cloning
 * annotations in found paths, before returning them in <code>findPath</code>.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class CloningGraph<N, A extends Copyable<A>> extends Graph<N, A> {

    /**
     * Constructs a new <code>CloningGraph</code>.
     * 
     * @param directed
     */
    public CloningGraph(boolean directed) {
        super(directed);
    }

    /**
     * Does exactly the same as the corresponding superclass method, except for
     * cloning the annotations before returning them.
     * 
     * @see at.iaik.suraq.util.graph.Graph#findPath(java.lang.Object,
     *      java.lang.Object)
     */
    @Override
    public List<A> findPath(N src, N dst) {

        List<A> annotations = super.findPath(src, dst);
        if (annotations == null)
            return null;
        assert (annotations != null);
        List<A> result = new ArrayList<A>(annotations.size());
        for (A annotation : annotations)
            result.add(annotation.clone());
        return result;
    }

}
