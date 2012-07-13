package at.iaik.suraq.main;

import java.util.ArrayList;
import java.util.List;

public class GraphElement {
    // TODO: comment
    
    private boolean visited = false;
    
    private List<GraphElement> neighbours = new ArrayList<GraphElement>();
    private String varname;
    
    public GraphElement(String varname)
    {
        this.varname = varname;
    }
    
    public boolean isVisited()
    {
        return visited;
    }
    public void setVisited(boolean visited)
    {
        this.visited = visited;
    }
    
    // Neighboor handling
    public List<GraphElement> getNeighbours()
    {
        return neighbours;
    }
    public void addNeighbour(GraphElement neighbour)
    {
        neighbours.add(neighbour);
    }
    public boolean isConnectedWith(GraphElement neighbor)
    {
        return neighbours.contains(neighbor);
    }

    // Varname handling
    public void setVarname(String varname)
    {
        this.varname = varname;
    }
    public String getVarname()
    {
        return this.varname;
    }
    
    @Override
    public String toString()
    {
        String ret = varname + " {";
        for(GraphElement neighbor : neighbours)
        {
            ret += neighbor.getVarname() + " ";
        }
        return ret + "}";
    }
    
}
