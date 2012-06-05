/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util.graph;

/**
 * An (annotated) edge in a graph.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
class AnnotatedEdge<N, A> {

    private final N src;

    private final N dst;

    private final A annotation;

    /**
     * Constructs a new <code>AnnotatedEdge</code>.
     * 
     * @param src
     * @param dst
     * @param annotation
     */
    public AnnotatedEdge(N src, N dst, A annotation) {
        assert (src != null);
        assert (dst != null);
        this.src = src;
        this.dst = dst;
        this.annotation = annotation;
    }

    /**
     * @return the <code>src</code>
     */
    public N getSrc() {
        return src;
    }

    /**
     * @return the <code>dst</code>
     */
    public N getDst() {
        return dst;
    }

    /**
     * @return the <code>annotation</code>
     */
    public A getAnnotation() {
        return annotation;
    }

}
