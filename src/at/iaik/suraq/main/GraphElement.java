/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.main;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * This is a class, needed for Graph Based Reduction to Propositional Logic. The
 * GraphElement symbolizes a vertex that has connections to its neighbours.
 * 
 * @author Hillebold Christoph
 * 
 */
public class GraphElement {
    // iterating through the GraphElement, it is useful to know which elements
    // already are visited
    private boolean visited = false;
    // it could also help to know if this Vertex was visited anytime before
    private boolean visited_once = false;
    // the neighbours of the GraphElement (equivalences with other variables in
    // the formula)
    private Map<GraphElement, String> neighbours = new HashMap<GraphElement, String>();
    // The varname of the vertex (it is truely a variable in the formula)
    private String varname;

    /**
     * Constructs a GraphElement out of a given varname
     * 
     * @param varname
     *            varname (probably) of a DomainVariable
     */
    public GraphElement(String varname) {
        this.varname = varname;
    }

    /**
     * indicates if the vertex was already visited. This flag can be set and
     * reset by calling setVisited
     * 
     * @return true if visited, false if not visited
     */
    public boolean isVisited() {
        return visited;
    }

    /**
     * Sets the isVisited-Flag of the vertex. This is useful for iterating
     * through the Graph to detect if we already was here.
     * 
     * @param visited
     *            true if visited, false if not visited
     */
    public void setVisited(boolean visited) {
        this.visited = visited;
        visited_once = visited_once || visited;
    }

    /**
     * Indicates if this Vertex was visited at least once. This flag cannot be
     * reset.
     * 
     * @return true if visited, false if not visited
     */
    public boolean isVisitedOnce() {
        return visited_once;
    }

    /**
     * Gets the name of the equivalence between this element and the given
     * neighbour. Both Neighbours knows this string, which is the same
     * 
     * @param neighbour
     * @return name of the equivalence to this neighbour
     */
    public String getEquivalenceName(GraphElement neighbour) {
        return neighbours.get(neighbour);
    }

    /**
     * Gets all neighbours of this Vertex (variable)
     * 
     * @return
     */
    public Set<GraphElement> getNeighbours() {
        return neighbours.keySet();
    }

    /**
     * Adds a neighbour to this vertex. The name of the equivalence to the
     * neighbour must also be provided
     * 
     * @param neighbour
     *            A neighbour GraphElement (vertex)
     * @param equivalenceName
     *            the name of the equivalence from this variable to the other.
     *            It must be the same in both directions.
     */
    public void addNeighbour(GraphElement neighbour, String equivalenceName) {
        neighbours.put(neighbour, equivalenceName);
    }

    /**
     * Checks whether this GraphElement is directly connected with the given
     * GraphElement
     * 
     * @param neighbor
     * @return
     */
    public boolean isConnectedWith(GraphElement neighbor) {
        return neighbours.containsKey(neighbor);
    }

    /**
     * Sets the varname of this GraphElement
     * 
     * @param varname
     */
    public void setVarname(String varname) {
        this.varname = varname;
    }

    /**
     * Gets the varname of this GraphElement
     * 
     * @return
     */
    public String getVarname() {
        return this.varname;
    }

    @Override
    public int hashCode() {
        return varname.hashCode();
    }

    @Override
    public String toString() {
        String ret = varname + " {";
        Object[] _neighbours = neighbours.keySet().toArray();
        int cnt = neighbours.keySet().size();
        for (int i = 0; i < cnt; i++) {
            GraphElement neighbor = (GraphElement) _neighbours[i];
            ret += neighbor.getVarname() + " ";
        }
        return ret + "}";
    }

}
