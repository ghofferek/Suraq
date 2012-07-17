package at.iaik.suraq.main;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.util.Util;

public class GraphReduction {

    private static boolean _isActive = true;
    private static boolean _debug = false;
    protected Map<Token, PropositionalVariable> prop_cache = new HashMap<Token, PropositionalVariable>();
    protected Map<EqualityFormula, String> replacements = null;
    protected Stack<GraphElement> visitedDFS = null;
    protected long circlecounter = 0;
    protected List<List<PropositionalVariable>> circles = null;
    
    
    /****************************************************************************************
     * Developer Notes:
     * - A large amount of code of this transformation is in EqualityFormula:replaceEquivalences
     * - There should not be any uninterpreted functions nor Arrays, etc. in the Formula
     * - There are two implementations of the GraphReduction:
     *    - one tries to find circles and builds only nessasary constraints
     *    - the other makes the graph chord-free and generates constraints for each triangle
     ****************************************************************************************/
    
    
    private PropositionalVariable generatePropositionalVariable(Token token)
    {
        if(prop_cache.containsKey(token))
        {
            return prop_cache.get(token);
        }
        PropositionalVariable p = new PropositionalVariable(token);
        prop_cache.put(token, p);
        return p;
    }
    
    public Formula perform(Formula formula, Set<Token> noDependenceVars) throws IOException
    {
        // isActive & Intro
        if(!_isActive)
        {
            System.err.println("GR: Didn't perform Graph-Based Reduction to Propositional Logic, because it is inactive.");
            return formula;
        }
        System.out.println("ImpliesFormulaGR: Welcome to the Graph-Based Reduction to Propositional Logic.");
        
        replacements = new TreeMap<EqualityFormula, String>();
        // do NOT clean up replacements, we need them later!
        
        // 1.1 find all equivalences, replace them by Propositional Vars with a new name
        // 1.2 save the replacements to the given structure
        // 1.3 set noDependenceVars for the replaced term if any containing term is noDepVar
        formula = formula.replaceEquivalences(formula, replacements, noDependenceVars);
        
        // 2.1 Build Graph
        Collection<GraphElement> vertices = generateGraph(replacements);

        System.out.println("GR: Built "+vertices.size()+" vertices out of "+replacements.keySet().size()+" replacements.");
        if(_debug)
        {
            for(GraphElement vertex : vertices)
            {
                System.out.println("Vertex: "+ vertex);
            }
        }
        if(vertices.size()==0)
        {
            System.out.println("GR: There were no equivalences in the Formula.");
            return formula;
        }

        Formula btrans = null;
        
        int method = 1;
        if(method == 1) // Try to find circles without making chord-free
        {
            System.out.println("GR: Try to find circles without making chord-free... ");
            btrans = generateBtransCircles(formula, vertices);
        }
        else if(method == 2) // make graph chord-free and find all triangles
        {
            System.out.println("GR: Make the Graph chord-free... ");
            makeChordFreeGraph(formula, vertices); // TODO: noDependenceVars setzen?
            
            System.out.println("GR: Find all triangles and generate Btrans... ");
            btrans = generateBtrans(vertices);
        }

        return new ImpliesFormula(btrans, formula);
    }
    
    public Formula generateBtrans(Collection<GraphElement> vertices) //throws IOException
    {
        long step = vertices.size() / 100;
        if(step==0) step=1;
        long cnt = 0;
        ArrayList<Formula> btransparts = new ArrayList<Formula>();
        btransparts.ensureCapacity(3*vertices.size());
        
        //File file = new File("./btrans.txt");
        //FileWriter fstream = new FileWriter(file);
        //fstream.write("and\n");

        for(GraphElement vertex : vertices)
        {
            if(cnt++ % step ==0)
            {
                System.out.println("GR: generateBtrans... (cur:" +btransparts.size() + ")" + cnt / step + "% von vertices#: "+vertices.size());
            }
            vertex.setVisited(false);
            //Set<GraphElement> neighbours = vertex.getNeighbours();
            int size = vertex.getNeighbours().size();
            Object[] neighbours = vertex.getNeighbours().toArray();
            
            for(int i=0;i<size;i++)
            {
                GraphElement ni = (GraphElement)neighbours[i];
                if(ni.isVisited())
                for(int j=i+1;j<size;j++)
                {
                    GraphElement nj = (GraphElement)neighbours[j];
                    if(nj.isVisited())
                    if(ni.isConnectedWith(nj)) // && || nj.isConnectedWith(ni)
                    {
                        // found a triangle: vertex - ni - nj
                        Token t1 = vertex.getToken(ni);
                        Token t2 = vertex.getToken(nj);
                        Token t3 = ni.getToken(nj);
                        btransparts.add(generateBtransElemCNF(t1, t2, t3));
                        btransparts.add(generateBtransElemCNF(t2, t3, t1));
                        btransparts.add(generateBtransElemCNF(t3, t1, t2));
                    }
                }
            }
            /*
            // save to file because we have too less memory
            try
            {
                // debug message
                System.out.println("* btrans #"+cnt+"/"+vertices.size()+": "+btransparts.size()+", neighbors: "+size);
                for(Formula formula : btransparts)
                {
                    fstream.write(formula.toString());
                }
                btransparts.clear();
            }
            catch(Exception ex)
            {
                ex.printStackTrace();
                throw new RuntimeException("FileError.");
            }
            */
        }
        //fstream.close();
        vertices = null;
        
        // for small examples
        return new AndFormula(btransparts);
        
        // for large examples
        //return new PropositionalVariable("Btrans");
    }
    
    protected OrFormula generateBtransElemCNF(Token a, Token b, Token c)
    {
        List<Formula> part1 = new ArrayList<Formula>(3);
        part1.add(new NotFormula(generatePropositionalVariable(a)));
        part1.add(new NotFormula(generatePropositionalVariable(b)));
        part1.add(generatePropositionalVariable(c));
        return new OrFormula(part1);
    }
    
    protected ImpliesFormula generateBtransElem(Token a, Token b, Token c)
    {
        List<Formula> part1 = new ArrayList<Formula>(2);
        part1.add(generatePropositionalVariable(a));
        part1.add(generatePropositionalVariable(b));
        AndFormula and = new AndFormula(part1);
        return new ImpliesFormula(and, generatePropositionalVariable(c));
    }
    
    
    protected Formula generateBtransCircles(Formula topLevelFormula, Collection<GraphElement> vertices)
    {
        // search for circles with DFS
        circlecounter = 0; // reset the counter
        visitedDFS = new Stack<GraphElement>();
        visitedDFS.ensureCapacity(vertices.size());
        circles = new ArrayList<List<PropositionalVariable>>();
        
        for(GraphElement vertex : vertices)
        {
            //if(!vertex.isVisited())
            {
                System.out.print("\n next: ");
                vertex.setVisited(true);
                depthFirstSearch(vertex, vertex, null);
            }
        }
        
        System.out.println("\nFinally there are "+ circlecounter+ " circles");
        
        List<Formula> btransList = new ArrayList<Formula>();
        for(List<PropositionalVariable> circle : circles)
        {
            int size = circle.size();
            for(int i=0; i<size; i++)
            {
                List<PropositionalVariable> newList = new ArrayList<PropositionalVariable>(circle);
                PropositionalVariable c = newList.remove(i);
                btransList.add(new ImpliesFormula(new AndFormula(newList), c));
            }
        }
        
        return new AndFormula(btransList);
    }

    protected void resetVisited(GraphElement current)
    {
        current.setVisited(false);
        for(GraphElement neighbour : current.getNeighbours())
        {
            if(neighbour.isVisited())
            {
                resetVisited(neighbour);
            }
        }
    }
    
    //protected int depthFirstSearch(GraphElement current, GraphElement last, int remainingDepth)
    protected void depthFirstSearch(GraphElement start, GraphElement current, GraphElement last)
    {
        //int minRemainingDepth = remainingDepth;
        current.setVisited(true);
        visitedDFS.push(current);
        for(GraphElement neighbour : current.getNeighbours())
        {
            if(neighbour != last)
            {
                if(visitedDFS.contains(neighbour))
                {
                    //if(remainingDepth == 0)
                    {
                        // we have had this neighbour - this is a circle
                        circlecounter++;
                        
                        if(circlecounter%10000==0)
                            System.out.print(" " + circlecounter);
                        int circle_start = visitedDFS.indexOf(neighbour);
                        int circle_end   = visitedDFS.size();
                        List<PropositionalVariable> circle = new ArrayList<PropositionalVariable>(circle_end-circle_start+1);
                        for(int i=circle_start; i<circle_end; i++)
                        {
                            int j = i + 1;
                            if(j==circle_end)
                                j = circle_start;
                            
                            GraphElement circle_elem = visitedDFS.get(i);
                            GraphElement next_elem = visitedDFS.get(j);
                            Token token =  circle_elem.getToken(next_elem);
                            PropositionalVariable pv = generatePropositionalVariable(token);
                            circle.add(pv);
                        }
      
                        circles.add(circle);
                    }
                }
                //else if(!neighbour.isVisited())
                else if(!visitedDFS.contains(neighbour) && !neighbour.isVisited())
                {
                    //if(remainingDepth > 0 && !neighbour.isVisited())
                    //if(!neighbour.isVisited())
                    {
                        // this is a new neighbor that was not visited until now
                        depthFirstSearch(start, neighbour, current);
                        //int tmp = depthFirstSearch(neighbour, current, remainingDepth-1);
                        //if(tmp < minRemainingDepth)
                         //   minRemainingDepth = tmp;
                    }
                }
            }
        }
        if(visitedDFS.pop()!=current)
        {
            throw new RuntimeException("DFS Search failed.");
        }
       // return minRemainingDepth;
    }
    
    public void makeChordFreeGraph(Formula topLevelFormula, Collection<GraphElement> vertices)
    {
        System.out.println("There are "+vertices.size()+" vertices.");
        long step = vertices.size() / 100 + 1;
        long cnt = 0;
        for(GraphElement vertex : vertices)
        {
            if(cnt++ % step ==0)
            {
                System.out.println("GR: makeChordFreeGraph... " + cnt / step + "%");
            }
            vertex.setVisited(true);
            //Set<GraphElement> neighbours = vertex.getNeighbours();
            int size = vertex.getNeighbours().size();
            Object[] neighbours = vertex.getNeighbours().toArray();
            for(int i=0;i<size;i++)
            {
                GraphElement ni = (GraphElement)neighbours[i];
                if(ni.isVisited()) // vertex was already "deleted"
                    continue;
                for(int j=i+1;j<size;j++)
                {
                    GraphElement nj = (GraphElement)neighbours[j];
                    if(nj.isVisited()) // vertex was already "deleted"
                        continue;
                    if(!ni.isConnectedWith(nj)) // && || nj.isConnectedWith(ni)
                    {
                        // add a chord
                        Token token = new Token(getVarName(topLevelFormula, ni.getVarname(), nj.getVarname()));
                        ni.addNeighbour(nj, token);
                        nj.addNeighbour(ni, token);
                    }
                }
            }
        }
    }
    
    public static String getVarName(Formula topLevelFormula, String ti, String tj)
    {
        if(ti.compareTo(tj)>0)
        {
            String help = tj;
            tj = ti;
            ti = help;
        }
        String newName = "eq_"+ti+"_"+tj;
        return Util.freshVarNameCached(topLevelFormula, newName);
    }
    
    /**
     * Generates a Graph out of given replacements. 
     * The vertices of the graph are the former variables and the connections are the equalities.
     * Every GraphElement in the Graph is a vertex and knows it's neighbours.
     * @param replacements
     * @return a Collection of vertices (former Variables) that are connected (former equalities)
     */
    public Collection<GraphElement> generateGraph(Map<EqualityFormula, String> replacements)
    {
        Map<String, GraphElement> vertices = new HashMap<String, GraphElement>();
        for(EqualityFormula replacement : replacements.keySet())
        {
            List<Term> terms = replacement.getTerms();
            if(terms.size() < 2)
            {
                throw new RuntimeException("GR: An equality had less than two subterms.");
            }
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
            
            Token token = new Token(replacements.get(replacement));
            g1.addNeighbour(g2, token);
            g2.addNeighbour(g1, token);
        }
        return vertices.values();
    }
    
    
    /** GETTER AND SETTER **/

    public static void setDebug(boolean isDebug)
    {
        _debug = isDebug;
    }
    public static boolean isDebug()
    {
        return _debug;
    }
    public static void setActive(boolean isActive)
    {
        _isActive = isActive;
    }
    public static boolean isActive()
    {
        return _isActive;
    }
    
    public Map<EqualityFormula, String> getReplacements()
    {
        return replacements;
    }
    
}
