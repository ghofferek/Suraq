package at.iaik.suraq.main;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.Vector;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.Util;

public class GraphReduction {

    private static boolean _isActive = true;
    
    private static boolean _additionalCircles = false; // TODO: activate this for extended circle algorithm
    private static boolean _debug = false;
    private static boolean _supportMultithreading = false;
    private static int _maxThreads = 2;
    protected Map<Token, PropositionalVariable> prop_cache = new HashMap<Token, PropositionalVariable>();
    protected Map<EqualityFormula, String> replacements = null;
    protected Stack<GraphElement> visitedDFS = null;
    protected long circlecounter = 0;
    protected final List<List<PropositionalVariable>> circles = new Vector<List<PropositionalVariable>>();
    protected final List<List<PropositionalVariable>> circles2 = new Vector<List<PropositionalVariable>>();
    

    // Hash of Hashset is the sum of the Hashes
    protected final HashSet<HashSet<PropositionalVariable>> hashCircles = new HashSet<HashSet<PropositionalVariable>>();
    protected List<GraphReductionThread> threads = null;
    
    
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
        PropositionalVariable p = (PropositionalVariable)FormulaCache.propVar.put(new PropositionalVariable(token));
        prop_cache.put(token, p);
        return p;
    }
    
    /**
     * computes stats in O(vertices.size()) time and prints to System.out
     * @param vertices
     */
    protected void writeStats(Collection<GraphElement> vertices)
    {
        int count = vertices.size();
        int sum_neighbours = 0;
        int min_neighbours = Integer.MAX_VALUE;
        int max_neighbours = Integer.MIN_VALUE;
        for(GraphElement vertex : vertices)
        {
            int neighbours = vertex.getNeighbours().size();
            sum_neighbours += neighbours;
            if(neighbours > max_neighbours)
                max_neighbours = neighbours;
            if(neighbours < min_neighbours)
                min_neighbours = neighbours;
        }
        int edges = sum_neighbours / 2;
        float average_neighbours = ((float)sum_neighbours) / ((float)count);
        
        
        System.out.println("***************************************************");
        System.out.println("* Statistic of Graph-based reduction to prop. logic");
        System.out.println("* - Count of vertices:  "+count);
        System.out.println("* - Count of edges:     "+edges);
        System.out.println("* - Average Neighbours: "+average_neighbours);
        System.out.println("* - Min. Neighbours:    "+min_neighbours);
        System.out.println("* - Max. Neighbours:    "+max_neighbours);
        System.out.println("***************************************************");
        
        if(_debug)
        {
            for(GraphElement vertex : vertices)
            {
                System.out.println("Vertex: "+ vertex);
            }
        }
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
        writeStats(vertices);

        Formula btrans = null;
        
        int method = 2; // FIXME: define method here, 2 is the only one working
        if(method == 1) // Try to find circles without making chord-free
        {
            System.out.println("GR: Try to find circles without making chord-free... ");
            btrans = generateBtransCircles(formula, vertices);
        }
        else if(method == 2 || method == 3) // make graph chord-free and find all triangles
        {
            System.out.println("GR: Make the Graph chord-free... ");
            makeChordFreeGraph(formula, vertices); // TODO: noDependenceVars setzen?
            writeStats(vertices);
            

            int countTriangles = countTriangles(vertices);
            System.out.println("GR: There are " + countTriangles + " triangles.");
            
            System.out.println("GR: Find all triangles and generate Btrans... ");
            if(method == 2)
            {
                btrans = generateBtrans(vertices);
            }
            else if(method == 3)
            {
                btrans = this.generateBtransToFile(vertices, "./btrans.txt");
            }
        }

        return new ImpliesFormula(btrans, formula);
    }

    protected int countTriangles(Collection<GraphElement> vertices) //throws IOException
    {
        for(GraphElement vertex : vertices)
        {
            resetVisited(vertex);
        }
   
        int count = 0;
        for(GraphElement vertex : vertices)
        {
            vertex.setVisited(true);
            
            int size = vertex.getNeighbours().size();
            Object[] neighbours = vertex.getNeighbours().toArray();
            
            for(int i=0;i<size;i++)
            {
                GraphElement ni = (GraphElement)neighbours[i];
                if(!ni.isVisited())
                for(int j=i+1;j<size;j++)
                {
                    GraphElement nj = (GraphElement)neighbours[j];
                    if(!nj.isVisited())
                    if(ni.isConnectedWith(nj)) // && || nj.isConnectedWith(ni)
                    {
                        count++;
                    }
                }
            }
        }

        return count;
    }
    protected Formula generateBtrans(Collection<GraphElement> vertices) //throws IOException
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

        // you can comment that in: only for debugging issues
        FormulaCache.printStatistic();
        
        return AndFormula.generate(btransparts);
        
        // for large examples if the btrans matrix is written to a file.
        //return new PropositionalVariable("Btrans");
        
    } // generateBtrans
    
    protected PropositionalVariable generateBtransToFile(Collection<GraphElement> vertices, String filename)
    {
        long step = vertices.size() / 1000;
        if(step==0) step=1;
        long cnt = 0;
        ArrayList<Formula> btransparts = new ArrayList<Formula>(3*vertices.size());

        File file = new File(filename);
        FileWriter fstream = null;
        try
        {
            fstream = new FileWriter(file);
            fstream.write("and\n");
    
            for(GraphElement vertex : vertices)
            {
                if(cnt++ % step == 0)
                {
                    System.out.println("GR: generateBtrans... (cur:" +btransparts.size() + ")" + 
                            (float)cnt / (float)step / 10.0 + "% von vertices#: "+vertices.size());
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
                            btransparts.add(generateBtransElem(t1, t2, t3));
                            btransparts.add(generateBtransElem(t2, t3, t1));
                            btransparts.add(generateBtransElem(t3, t1, t2));
                        }
                    }
                }
                
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
                    throw new RuntimeException("FileError");
                }
            }
        }
        catch(IOException ex)
        {
            ex.printStackTrace();
        }
        finally
        {
            try{
                if(fstream != null)
                    fstream.close();
            }
            catch(IOException ex2)
            {   
                ex2.printStackTrace();
            }
        }
        vertices = null;
        btransparts = null;
        
        return new PropositionalVariable("Btrans");
        
        
    } // generateBtransToFile
    
    protected OrFormula generateBtransElemCNF(Token a, Token b, Token c)
    {
        List<Formula> part1 = new ArrayList<Formula>(3);
        part1.add(FormulaCache.notFormula.put(new NotFormula(generatePropositionalVariable(a))));
        part1.add(FormulaCache.notFormula.put(new NotFormula(generatePropositionalVariable(b))));
        part1.add(generatePropositionalVariable(c));
        OrFormula or = FormulaCache.orFormula.put(OrFormula.generate(part1));
        return or;
    }
    
    protected ImpliesFormula generateBtransElem(Token a, Token b, Token c)
    {
        List<Formula> part1 = new ArrayList<Formula>(2);
        part1.add(generatePropositionalVariable(a));
        part1.add(generatePropositionalVariable(b));
        AndFormula and = FormulaCache.andFormula.put(AndFormula.generate(part1));
        ImpliesFormula implies = FormulaCache.impliesFormula.put(new ImpliesFormula(and, generatePropositionalVariable(c)));
        return implies;
    }
    
    protected Formula generateBtransCircles(Formula topLevelFormula, Collection<GraphElement> vertices)
    {
        // search for circles with DFS
        circlecounter = 0; // reset the counter
        visitedDFS = new Stack<GraphElement>();
        visitedDFS.ensureCapacity(vertices.size());

        circles.clear();
        circles2.clear();
        
        for(GraphElement vertex : vertices)
        {
            //if(!vertex.isVisitedOnce())
            {
                System.out.print("\n next:");
                this.resetVisited(vertex);
                vertex.setVisited(true);
                //depthFirstSearch(vertex, vertex, null);
                depthFirstSearchHash(vertex, vertex, null);
            }
        }
        circles.addAll(circles2);
        circles2.clear();
        System.out.println("\nThere are "+ circlecounter+ " circles");
        
        // may one iteration be enough?
        // Runtime: O(circles^2 * elementspercircle^2)
        // Memory: O(circles^2 * elementspercircle)
        int circlesize = circles.size();
        if(_additionalCircles)
        {
            if(_supportMultithreading)
            {
                int cpus = Runtime.getRuntime().availableProcessors();
                if(cpus > _maxThreads)
                    _maxThreads = cpus-1;
                
                int singleSize = circlesize / _maxThreads;
                int last_index = 0;
                threads = new ArrayList<GraphReductionThread>();
                for(int i=1; i<=_maxThreads; i++)
                {
                    int index = singleSize * i;
                    if(i == _maxThreads) // the last Thread takes the rest
                        index = circlesize;
                    threads.add(new GraphReductionThread(this, last_index, index));
                    last_index = index;
                }
                for(int i=0; i<_maxThreads; i++)
                {
                    System.out.println("Starting Thread...");
                    threads.get(i).start();
                }
                for(int i=0; i<_maxThreads; i++)
                {
                    try
                    {
                        threads.get(i).join();
                        System.out.println("Thread joined");
                    }
                    catch (InterruptedException e)
                    {
                        e.printStackTrace();
                    }
                }
                threads.clear();
            }
            else
            {
                for(int i=0; i<circlesize; i++)
                {
                    System.out.println("Search Circles #"+i+"/"+circlesize+" Circles: "+circlecounter); 
                    for(int j=i+1; j<circlesize; j++)
                    {
                        getSubFormula(circles.get(i), circles.get(j));
                    }
                }
            }
            circles.addAll(circles2);
            circles2.clear();
            
            System.out.println("\nFinally there are "+ circlecounter+ " circles");
        }
        
        // generate Btrans
        List<Formula> btransList = new ArrayList<Formula>();
        System.out.println("#circles: " + circles.size());
        for(List<PropositionalVariable> circle : circles)
        {
            int size = circle.size();
            for(int i=0; i<size; i++)
            {
                List<PropositionalVariable> newList = new ArrayList<PropositionalVariable>(circle);
                PropositionalVariable c = newList.remove(i);
                btransList.add(new ImpliesFormula(AndFormula.generate(newList), c));
            }
        }

        System.out.println("#hashCircles: " + hashCircles.size());
        for(HashSet<PropositionalVariable> circle : hashCircles)
        {
            int size = circle.size();
            for(int i=0; i<size; i++)
            {
                List<PropositionalVariable> newList = new ArrayList<PropositionalVariable>(circle);
                PropositionalVariable c = newList.remove(i);
                btransList.add(new ImpliesFormula(AndFormula.generate(newList), c));
            }
        }
        
        return AndFormula.generate(btransList);
    } // generateBtransCircles

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
    
    /**
     * The idea of this Method is to compare each two circles found and find common strings.
     * By doing so, additional circles can be found and added to the circlelist.
     * I assume, that this is not finding all circles either, but it found most nessasary circles.
     * This algorithm defenitely fails if the datastructure of the circles is a HashList, because it needs to be sorted.
     * At least it requires the elements in the same order
     * @param circle1
     * @param circle2
     * @return
     */
    protected List<PropositionalVariable> getSubFormula(List<PropositionalVariable> circle1, List<PropositionalVariable> circle2)
    {
        int csize1 = circle1.size();
        int csize2 = circle2.size();

        // Annahmen durch vorhergehende Algorithmen:
        // jedes element im circle kommt max. 1x vor!!!
        // daher kann bei gemeinsamkeiten i und j erhöht werden!!!
        // auch sind nie zwei circles vollständig identisch (while-endlosschleife)
        for(int forward = -1; forward <2; forward+=2) // {-1,+1}
        {
            for(int i=0; i<csize1; i++)
            {
                for(int j=i; j<csize2; j++)
                {
                    // interessant sind nur teilfolgen größer gleich 3...
                    if(circle1.get(i).equals(circle2.get(j)))
                    if(circle1.get((i+1)%csize1).equals(circle2.get((j+1*forward+csize2)%csize2)))
                    if(circle1.get((i+2)%csize1).equals(circle2.get((j+2*forward+csize2)%csize2))) 
                    {
                        int i_start = i;
                        int j_start = j;
                        int circle_size=0;
                        while(circle1.get((i)%csize1).equals(circle2.get((j+csize2)%csize2)))
                        {
                            circle_size++;
                            i++;
                            j+=forward;
                        }
                        if(_debug)
                            System.out.println("Found duplicate circle of size " + circle_size);
                        List<PropositionalVariable> new_circle = new ArrayList<PropositionalVariable>(circle_size);
                        // copy everything from the end of the common term (incl. the last common term)
                        // to the first common term (incl.)
                        for(int copy_i=i-csize1-1; copy_i<=i_start; copy_i++)
                        {
                            new_circle.add(circle1.get((copy_i+csize1) % csize1));
                        }
                        
                        // now copy from the second circle everything from the last common term (excl.)
                        // to the first common term (excl.)
                        if(forward == 1)
                        {
                            for(int copy_j=j-csize2; j<j_start; j++)
                            {
                                new_circle.add(circle2.get((copy_j+csize2) % csize2));
                            }
                        }
                        else // if(foward == -1)
                        {
                            for(int copy_j=j+csize2; j>j_start; j--)
                            {
                                new_circle.add(circle2.get((copy_j+csize2) % csize2));
                            }
                        }
                        this.addCircle(new_circle);
                        // TODO: evtl. return hier?
                        //return null; // seems to work for median tests
                    }
                }
            }
        }
        
        
        return null;
    } // getSubFormula
    
    //protected int depthFirstSearch(GraphElement current, GraphElement last, int remainingDepth)
    protected void depthFirstSearchHash(GraphElement start, GraphElement current, GraphElement last)
    {
        // TODO: improve here!!!
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
                        
                        int circle_start = visitedDFS.indexOf(neighbour);
                        int circle_end   = visitedDFS.size();
                        HashSet<PropositionalVariable> circle = new HashSet<PropositionalVariable>(circle_end-circle_start+1);
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
          
                        this.addHashCircle(circle);
                    }
                }
                //else
                else if(!neighbour.isVisited())
                //else if(!visitedDFS.contains(neighbour) && !neighbour.isVisited())
                {
                    //if(remainingDepth > 0 && !neighbour.isVisited())
                    //if(!neighbour.isVisited())
                    {
                        // this is a new neighbor that was not visited until now
                        depthFirstSearchHash(start, neighbour, current);
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
        
    } // depthFirstSearchHash
    
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
          
                        this.addCircle(circle);
                    }
                }
                else if(!neighbour.isVisited())
                //else if(!visitedDFS.contains(neighbour) && !neighbour.isVisited())
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
        
    } // depthFirstSearch
    
    protected void makeChordFreeGraph(Formula topLevelFormula, Collection<GraphElement> vertices)
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
                // there is no such Vertex :-(
                //if(ni.getNeighbours().size()<2)
                //{
                //	System.err.print('+');
                //	continue;
                //}
                for(int j=i+1;j<size;j++)
                {
                    GraphElement nj = (GraphElement)neighbours[j];
                    if(nj.isVisited()) // vertex was already "deleted"
                        continue;

                    // there is no such Vertex :-(
                    //if(nj.getNeighbours().size()<2) // not nessasary to connect this one
                    //{
                    //	System.err.print('+');
                    //	continue;
                    //}
                    if(!ni.isConnectedWith(nj)) // && || nj.isConnectedWith(ni)
                    {
                        // add a chord
                        Token token = Token.generate(getVarName(topLevelFormula, ni.getVarname(), nj.getVarname()));
                        ni.addNeighbour(nj, token);
                        nj.addNeighbour(ni, token);
                    }
                }
            }
        }
    } // makeChordFreeGraph
    
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
    protected Collection<GraphElement> generateGraph(Map<EqualityFormula, String> replacements)
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
            
            Token token = Token.generate(replacements.get(replacement));
            g1.addNeighbour(g2, token);
            g2.addNeighbour(g1, token);
        }
        return vertices.values();
    } // generateGraph
    
    
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
        if(isActive == false)
            System.err.println("GraphReduction was set inactive.");
        else
            System.err.println("GraphReduction was set active.");
            
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
    public synchronized List<List<PropositionalVariable>> getCircles()
    {
        return circles;
    }
    public synchronized void addCircle(List<PropositionalVariable> circle)
    {
        circlecounter++;
        circles2.add(circle);
        if(circlecounter%10000==0)
            System.out.print(" " + circlecounter);
    }   
    
    private int stat_failed = 0;
    public synchronized void addHashCircle(HashSet<PropositionalVariable> circle)
    {
        if(!hashCircles.contains(circle))
        {
            circlecounter++;
            hashCircles.add(circle);
            if(circlecounter%10000==0)
                System.out.print(" " + circlecounter);
        }
        else
        {
            stat_failed++;
            if(stat_failed%10000==0)
                System.out.print(" [" + stat_failed+"]");
        }
    }
    public synchronized List<GraphReductionThread> getThreads()
    {
        return threads;
    }
    
}
