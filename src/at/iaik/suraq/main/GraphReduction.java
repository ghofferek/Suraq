package at.iaik.suraq.main;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;

public class GraphReduction {

    private static boolean _isActive = true;
    public static void setActive(boolean isActive)
    {
        _isActive = isActive;
    }
    public static boolean isActive()
    {
        return _isActive;
    }
    
    /****************************************************************************************
     * Developer Notes:
     * - A large amount of code of this transformation is in EqualityFormula:replaceEquivalences
     * - There should not be any uninterpreted functions nor Arrays, etc. in the Formula
     ****************************************************************************************/
    
    
    public GraphReduction()
    {
        
    }
    
    public Formula perform(Formula formula, Set<Token> noDependenceVars)
    {
        // isActive & Intro
        if(!_isActive)
        {
            System.err.println("GR: Didn't perform Graph-Based Reduction to Propositional Logic, because it is inactive.");
            return formula;
        }
        System.out.println("GR: Welcome to the Graph-Based Reduction to Propositional Logic.");
        
        Map<EqualityFormula, String> replacements = new TreeMap<EqualityFormula, String>();
        
        // 1.1 find all equivalences, replace them by Propositional Vars with a new name
        // 1.2 save the replacements to the given structure
        // 1.3 set noDependenceVars for the replaced term if any containing term is noDepVar
        formula = formula.replaceEquivalences(formula, replacements, noDependenceVars);
        
        // 2.1 Build Graph
        Collection<GraphElement> vertices = generateGraph(replacements.keySet());
        System.out.println("GR: Built "+vertices.size()+" vertices out of "+replacements.keySet().size()+" replacements.");
        for(GraphElement vertex : vertices)
        {
            System.out.println("Vertex: "+ vertex);
        }
        
        System.out.println("GR: Make the Graph cord-free.");
        makeChordFreeGraph(vertices);

        System.out.println("GR: Find all triangles and generate Btrans");
        
        return formula;
    }
    
    public void generateBtrans(Collection<GraphElement> vertices)
    {
        for(GraphElement vertex : vertices)
        {
            List<GraphElement> neighbours = vertex.getNeighbours();
            for(int i=0;i<neighbours.size();i++)
            {
                GraphElement ni = neighbours.get(i);
                for(int j=i+1;j<neighbours.size();j++)
                {
                    GraphElement nj = neighbours.get(j);
                    if(ni.isConnectedWith(nj)) // && || nj.isConnectedWith(ni)
                    {
                        // found a triangle: vertex - ni - nj
                        
                    }
                }
            }
        }
    }
    
    protected ImpliesFormula generateBtransElem(GraphElement a, GraphElement b, GraphElement c)
    {
        List<Formula> part1 = new ArrayList<Formula>();
        part1.add(new PropositionalVariable(a.getVarname()));
        part1.add(new PropositionalVariable(b.getVarname()));
        AndFormula and = new AndFormula(part1);
        return new ImpliesFormula(and, new PropositionalVariable(c.getVarname()));
    }
    
    public void makeChordFreeGraph(Collection<GraphElement> vertices)
    {
        for(GraphElement vertex : vertices)
        {
            vertex.setVisited(true);
            List<GraphElement> neighbours = vertex.getNeighbours();
            for(int i=0;i<neighbours.size();i++)
            {
                GraphElement ni = neighbours.get(i);
                if(ni.isVisited()) // vertex was already "deleted"
                    continue;
                for(int j=i+1;j<neighbours.size();j++)
                {
                    GraphElement nj = neighbours.get(j);
                    if(nj.isVisited()) // vertex was already "deleted"
                        continue;
                    if(!ni.isConnectedWith(nj)) // && || nj.isConnectedWith(ni)
                    {
                        // add a chord
                        ni.addNeighbour(nj);
                        nj.addNeighbour(ni);
                    }
                }
            }
        }
    }
    
    public Collection<GraphElement> generateGraph(Set<EqualityFormula> replacements)
    {
        Map<String, GraphElement> vertices = new TreeMap<String, GraphElement>();
        for(EqualityFormula replacement : replacements)
        {
            List<Term> terms = replacement.getTerms();
            String name1 = terms.get(0).toString();
            String name2 = terms.get(1).toString();
            
            GraphElement g1;
            if(vertices.containsKey(name1))
            {
                g1 = vertices.get(name1);
            }
            else
            {
                g1 = new GraphElement(name1);
                vertices.put(name1, g1);
            }
            
            GraphElement g2;
            if(vertices.containsKey(name2))
            {
                g2 = vertices.get(name2);
            }
            else
            {
                g2 = new GraphElement(name2);
                vertices.put(name2, g2);
            }
            
            g1.addNeighbour(g2);
            g2.addNeighbour(g1);
        }
        return vertices.values();
    }
    
}
