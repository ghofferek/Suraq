/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util.graph;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * A simple graph with generic nodes.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class Graph<N, A> {

    private final Set<N> nodes = new HashSet<N>();

    private final Set<AnnotatedEdge<N, A>> edges = new HashSet<AnnotatedEdge<N, A>>();

    private final boolean directed;

    public Graph() {
        this(false);
    }

    public Graph(boolean directed) {
        this.directed = directed;
    }

    public void addNode(N node) {
        if (!nodes.contains(node)) {
            nodes.add(node);
        }
    }

    public void addEdge(N src, N dst) {
        this.addEdge(src, dst, null);
    }

    public void addEdge(N src, N dst, A annotation) {
        this.addNode(src);
        this.addNode(dst);
        this.addDirectedEdge(src, dst, annotation);
        if (!this.directed)
            this.addDirectedEdge(dst, src, annotation);
    }

    private void addDirectedEdge(N src, N dst, A annotation) {
        assert (nodes.contains(src));
        assert (nodes.contains(dst));
        edges.add(new AnnotatedEdge<N, A>(src, dst, annotation));
    }

    /**
     * Finds a path from <code>src</code> to <code>dst</code> in the graph and
     * returns the annotations of the edges along the path.
     * 
     * @param src
     * @param dst
     * @return Annotations along a path from <code>src</code> to
     *         <code>dst</code>, or <code>null</code> if no such path exists.
     */
    public List<A> findPath(N src, N dst) {
        List<AnnotatedEdge<N, A>> path = new ArrayList<AnnotatedEdge<N, A>>();
        if (!nodes.contains(src) || !nodes.contains(dst))
            return null;

        for (AnnotatedEdge<N, A> edge : edges) {
            if (!edge.getSrc().equals(src))
                continue;
            path.add(edge);
            if (edge.getDst().equals(dst))
                break;
            path = this.findPath(path, dst);
            if (path.size() > 0)
                break;
        }

        if (path.size() == 0)
            return null;

        List<A> result = new ArrayList<A>();
        for (AnnotatedEdge<N, A> edge : path)
            result.add(edge.getAnnotation());
        return result;

    }

    private List<AnnotatedEdge<N, A>> findPath(
            List<AnnotatedEdge<N, A>> prefix, N dst) {
        List<AnnotatedEdge<N, A>> result;

        Set<N> visited = new HashSet<N>();
        for (AnnotatedEdge<N, A> edge : prefix) {
            visited.add(edge.getSrc());
            visited.add(edge.getDst());
        }

        N current = prefix.get(prefix.size() - 1).getDst();
        for (AnnotatedEdge<N, A> edge : edges) {
            if (!edge.getSrc().equals(current))
                continue;
            if (edge.getDst().equals(dst)) {
                result = new ArrayList<AnnotatedEdge<N, A>>(prefix);
                result.add(edge);
                return result;
            }

            if (visited.contains(edge.getDst()))
                continue;

            prefix.add(edge);
            List<AnnotatedEdge<N, A>> path = findPath(prefix, dst);
            if (path.size() > 0) {
                assert (path.get(path.size() - 1).getDst().equals(dst));
                return path;
            }
            prefix.remove(edge);

        }
        return new ArrayList<AnnotatedEdge<N, A>>(0);
    }

}
