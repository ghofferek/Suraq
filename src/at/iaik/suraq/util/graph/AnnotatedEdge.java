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

    private final int hash;

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

        this.hash = src.hashCode() ^ dst.hashCode() ^ annotation.hashCode();
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

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.hash;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof AnnotatedEdge))
            return false;

        if (!((AnnotatedEdge<?, ?>) obj).src.equals(this.src))
            return false;

        if (!((AnnotatedEdge<?, ?>) obj).dst.equals(this.dst))
            return false;

        if (!((AnnotatedEdge<?, ?>) obj).annotation.equals(this.annotation))
            return false;

        return true;
    }

}
