package at.iaik.suraq.main;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import at.iaik.suraq.sexp.Token;

public class GraphElement{
    // TODO: comment
    
    private boolean visited = false;
    private boolean visited_once = false;
    private Map<GraphElement, Token> neighbours = new HashMap<GraphElement, Token>();
    private String varname;
    private int distance;
    
    public int getDistance() {
        return distance;
    }

    public void setDistance(int distance) {
        this.distance = distance;
    }

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
        if(visited == true)
            visited_once = true;
    }
    public boolean isVisitedOnce()
    {
        return visited_once;
    }
    
    // Neighboor handling
    /*public Map<GraphElement, Token> getNeighbours()
    {
        return neighbours;
    }*/
    
    public Token getToken(GraphElement neighbour)
    {
        return neighbours.get(neighbour);
    }
    
    public Set<GraphElement> getNeighbours()
    {
        return neighbours.keySet();
    }
    public void addNeighbour(GraphElement neighbour, Token token)
    {
        neighbours.put(neighbour, token);
    }
    public boolean isConnectedWith(GraphElement neighbor)
    {
        return neighbours.containsKey(neighbor);
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
        /*for(GraphElement neighbor : neighbours.keySet().iterator())
        {
            ret += neighbor.getVarname() + " ";
        }
        */ // TODO repair
        return ret + "}";
    }

    
}
