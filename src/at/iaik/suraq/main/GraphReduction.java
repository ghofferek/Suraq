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
    // this flag activates or deactivates the GraphReduction globally
    private static boolean _isActive = true;
    // activates some unnessasary debug output - only use if you debug the GraphReduction
    private static boolean _debug = false;
    // not used: activate this to activate circle finding after the basic algorithm.
    private static boolean _additionalCircles = false;
    // not used: finding additional Circles is implemented using MultiThreading to reduce execution time
    private static boolean _supportMultithreading = false;
    // not used: --"--
    protected List<GraphReductionThread> threads = null;
    // not used: using Multithreading on finding additional circles there is a max. count of Threads
    // this value is overwritten, if the cpu has more than 2 cores: we use n-1 threads!
    private static int _maxThreads = 2;
    
    // a cache for PropositionalVariables using their name as a key
    protected Map<String, PropositionalVariable> propCache = new HashMap<String, PropositionalVariable>();
    // this stores the made replacements for further use
    // maybe you want to invert this Map to Map<String, EqualityFormula>
    protected Map<EqualityFormula, String> replacements = null;
    
    // not used: this is currently not used but still in the code for DepthFirstSearch in the Graph
    protected Stack<GraphElement> visitedDFS = null;
    // used for counting the found circles
    protected long circlecounter = 0;
    
    // Store for all found circles
    protected final List<List<PropositionalVariable>> circles = new Vector<List<PropositionalVariable>>();
    // Temporary store for all found circles. Transfered to circles and cleaned.
    protected final List<List<PropositionalVariable>> circles2 = new Vector<List<PropositionalVariable>>();
    // Store for storing circles in a hashSet (so they should be unique). Hash of Hashset is the sum of the Hashes
    // we could overthink this, but I think the HashSets should have the same order.
    protected final HashSet<HashSet<PropositionalVariable>> hashCircles = new HashSet<HashSet<PropositionalVariable>>();
    
    
    /****************************************************************************************
     * Developer Notes:
     * - A large amount of code of this transformation is in EqualityFormula:replaceEquivalences
     * - There should not be any uninterpreted functions nor Arrays, etc. in the Formula
     * - There are two implementations of the GraphReduction:
     *    - one tries to find circles and builds only nessasary constraints
     *    - the other makes the graph chord-free and generates constraints for each triangle
     ****************************************************************************************/
    
    
    private PropositionalVariable generatePropositionalVariable(
            String equivalenceName) {
        if (propCache.containsKey(equivalenceName)) {
            return propCache.get(equivalenceName);
        }
        PropositionalVariable p = (PropositionalVariable) PropositionalVariable
                .create(equivalenceName);
        propCache.put(equivalenceName, p);
        return p;
    }

    /**
     * computes Statistics in O(vertices.size()) time and prints to System.out
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
    
    /**
     * Performs the Graph Based Reduction to Propositional Logic
     * @param formula
     * @param noDependenceVars
     * @return
     * @throws IOException
     */
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
        
        int method = 2; // define method here, 2 is the only one working
        if(method == 1) // Try to find circles without making chordal
        {
            System.out.println("GR: Try to find circles without making chord-free... ");
            btrans = generateBtransCircles(formula, vertices);
        }
        else if(method == 2 || method == 3) // make graph chordal and find all triangles
        {
            System.out.println("GR: Make the Graph chord-free... ");
            makeGraphChordal(formula, vertices);
            writeStats(vertices);
            
            int countTriangles = countTriangles(vertices);
            System.out.println("GR: There are " + countTriangles + " triangles.");
            System.out.println("GR: Find all triangles and generate Btrans... ");
            
            if(method == 2)
            {
                btrans = generateBtrans(vertices);
            }
            else if(method == 3) // warning: this can easily be several GB...
            {
                btrans = this.generateBtransToFile(vertices, "./btrans.txt");
            }
        }
        
        // delete all NoDepVars that are not propositional vars
        HashSet<Token> toDelete = new HashSet<Token>(noDependenceVars);
        toDelete.removeAll(formula.getPropositionalVariables());
        noDependenceVars.removeAll(toDelete);

        return ImpliesFormula.create(btrans, formula);
    }

    /**
     * Counts all unique Triangle
     * @param vertices
     * @return
     */
    protected int countTriangles(Collection<GraphElement> vertices) {
        // reset the visited flag of the vertices
        for (GraphElement vertex : vertices) {
            resetVisited(vertex);
        }

        int count = 0;
        // go through all vertices and see if their neighbours are connected
        for (GraphElement vertex : vertices) {
            // "remove" the watched element by setting it visited.
            vertex.setVisited(true);

            int size = vertex.getNeighbours().size();
            Object[] neighbours = vertex.getNeighbours().toArray();

            // are any two neighbours connected with each other?
            // then we would have found a triangle
            for (int i = 0; i < size; i++) {
                GraphElement ni = (GraphElement) neighbours[i];
                if (!ni.isVisited())
                    for (int j = i + 1; j < size; j++) {
                        GraphElement nj = (GraphElement) neighbours[j];
                        if (!nj.isVisited())
                            if (ni.isConnectedWith(nj)) {
                                count++;
                            }
                    }
            }
        }
        return count;
    }
    
    /**
     * Generates the Btrans-Formula out of the given vertices that are chordal.
     * All Vertices must be VISITED before calling this method!
     * This method sets all vertices to UNVISITED again.
     * @param vertices
     * @return Btrans-Formula
     */
    protected Formula generateBtrans(Collection<GraphElement> vertices) //throws IOException
    {
        // for progress statistic during the algorithm:
        long step = vertices.size() / 100;
        if(step==0) step=1; // to avoid divide by zero error
        long cnt = 0;
        
        // collect all triangles
        ArrayList<Formula> btransparts = new ArrayList<Formula>();
        btransparts.ensureCapacity(3*vertices.size());
        
        for(GraphElement vertex : vertices)
        {
            if(cnt++ % step ==0)
            {
                System.out.println("GR: generateBtrans... (cur:" +btransparts.size() + ")" + cnt / step + "% von vertices#: "+vertices.size());
            }
            vertex.setVisited(false);
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
                        String t1 = vertex.getEquivalenceName(ni);
                        String t2 = vertex.getEquivalenceName(nj);
                        String t3 = ni.getEquivalenceName(nj);
                        btransparts.add(generateBtransElemCNF(t1, t2, t3));
                        btransparts.add(generateBtransElemCNF(t2, t3, t1));
                        btransparts.add(generateBtransElemCNF(t3, t1, t2));
                    }
                }
            }
        }
        vertices = null;
        
        // Statistic
        FormulaCache.printStatistic();
        
        return AndFormula.generate(btransparts);
        
    } // generateBtrans
    
    /**
     * writes the Btrans-Formula out to a given file and returns a PropositionalVariable 'Btrans' instead.
     * @param vertices
     * @param filename output file of the Btrans-Formula
     * @return a PropositionalVariable 'Btrans'
     */
    protected PropositionalVariable generateBtransToFile(Collection<GraphElement> vertices, String filename)
    {
        // for progress statistic during the algorithm:
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
                        if(ni.isConnectedWith(nj))
                        {
                            // found a triangle: vertex - ni - nj
                            String t1 = vertex.getEquivalenceName(ni);
                            String t2 = vertex.getEquivalenceName(nj);
                            String t3 = ni.getEquivalenceName(nj);
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
                    // and clear the buffer!!!
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
        
        return PropositionalVariable.create("Btrans");
        
        
    } // generateBtransToFile
    
    /**
     * Helps to generate the Btrans-Formula out of a triangle in CNF (!a v !b v c)
     * @param a
     * @param b
     * @param c
     * @return
     */
    protected OrFormula generateBtransElemCNF(String a, String b, String c)
    {
        List<Formula> part1 = new ArrayList<Formula>(3);
        part1.add(NotFormula.create(generatePropositionalVariable(a)));
        part1.add(NotFormula.create(generatePropositionalVariable(b)));
        part1.add(generatePropositionalVariable(c));
        OrFormula or = OrFormula.generate(part1);
        return or;
    }
    
    /**
     * Helps to generate the Btrans-Formula out of a triangle (a ^ b => c) 
     * @param a
     * @param b
     * @param c
     * @return
     */
    protected ImpliesFormula generateBtransElem(String a, String b, String c) {
        List<Formula> part1 = new ArrayList<Formula>(2);
        part1.add(generatePropositionalVariable(a));
        part1.add(generatePropositionalVariable(b));
        AndFormula and = AndFormula.generate(part1);
        ImpliesFormula implies = ImpliesFormula.create(and,
                generatePropositionalVariable(c));
        return implies;
    }
    
    /**
     * Resets the isVisited Flag of each vertex recursively
     * @param current
     */
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
     * Makes the Graph chordal
     * 
     * @param topLevelFormula
     * @param vertices
     */
    protected void makeGraphChordal(Formula topLevelFormula,
            Collection<GraphElement> vertices) {
        System.out.println("There are " + vertices.size() + " vertices.");

        // for progress statistics during the algorithm:
        long step = vertices.size() / 100 + 1;
        long cnt = 0;

        for (GraphElement vertex : vertices) {
            if (cnt++ % step == 0) {
                System.out.println("GR: makeChordFreeGraph... " + cnt / step
                        + "%");
            }
            vertex.setVisited(true);
            int size = vertex.getNeighbours().size();
            Object[] neighbours = vertex.getNeighbours().toArray();
            for (int i = 0; i < size; i++) {
                GraphElement ni = (GraphElement) neighbours[i];
                if (ni.isVisited()) // vertex was already "deleted" (visited)
                    continue;

                for (int j = i + 1; j < size; j++) {
                    GraphElement nj = (GraphElement) neighbours[j];
                    if (nj.isVisited()) // vertex was already "deleted"
                        continue;

                    if (!ni.isConnectedWith(nj)) // && || nj.isConnectedWith(ni)
                    {
                        // add a chord
                        String token = getVarName(topLevelFormula,
                                ni.getVarname(), nj.getVarname());
                        ni.addNeighbour(nj, token);
                        nj.addNeighbour(ni, token);
                    }
                }
            }
        }
    } // makeChordFreeGraph

    /**
     * Generates a name for the Equivalence between the two variables ti and tj.
     * The Result of this method is unique, regardless of the order of ti and tj.
     * @param topLevelFormula
     * @param ti name of the variable 1
     * @param tj name of the variable 2
     * @return name for the Equivalence between the two variables ti and tj
     */
    public static String getVarName(Formula topLevelFormula, String ti,
            String tj) {
        // sort the two strings, so that the result is everytime the same
        if (ti.compareTo(tj) > 0) {
            String help = tj;
            tj = ti;
            ti = help;
        }
        String newName = "eq_" + ti + "_" + tj;
        return Util.freshVarNameCached(topLevelFormula, newName);
    }
    
    /**
     * Generates a Graph out of given replacements. The vertices of the graph
     * are the former variables and the connections are the equalities. Every
     * GraphElement in the Graph is a vertex and knows it's neighbours.
     * 
     * @param replacements
     * @return a Collection of vertices (former Variables) that are connected
     *         (former equalities)
     */
    protected Collection<GraphElement> generateGraph(
            Map<EqualityFormula, String> replacements) {
        Map<String, GraphElement> vertices = new HashMap<String, GraphElement>();
        for (EqualityFormula replacement : replacements.keySet()) {
            List<Term> terms = replacement.getTerms();
            if (terms.size() < 2) {
                throw new RuntimeException(
                        "GR: An equality had less than two subterms.");
            }
            
            // Look for a matching vertex for the first variable
            String name1 = terms.get(0).toString();
            GraphElement g1;
            if (vertices.containsKey(name1)) {
                g1 = vertices.get(name1);
            } else {
                g1 = new GraphElement(name1);
                vertices.put(name1, g1);
            }

            // Look for a matching vertex for the second variable
            String name2 = terms.get(1).toString();
            GraphElement g2;
            if (vertices.containsKey(name2)) {
                g2 = vertices.get(name2);
            } else {
                g2 = new GraphElement(name2);
                vertices.put(name2, g2);
            }

            String token = replacements.get(replacement);
            g1.addNeighbour(g2, token);
            g2.addNeighbour(g1, token);
        }
        return vertices.values();
    } // generateGraph
    

    /////////////////////////////////////////////////////////////////////////
    /////////////////////////////////////////////////////////////////////////
    //// GETTER AND SETTER
    /////////////////////////////////////////////////////////////////////////
    /////////////////////////////////////////////////////////////////////////
    
    public static void setDebug(boolean isDebug) {
        _debug = isDebug;
    }

    public static boolean isDebug() {
        return _debug;
    }

    public static void setActive(boolean isActive) {
        if (isActive == false)
            System.err.println("GraphReduction was set inactive.");
        else
            System.err.println("GraphReduction was set active.");

        _isActive = isActive;
    }

    public static boolean isActive() {
        return _isActive;
    }

    public Map<EqualityFormula, String> getReplacements() {
        return replacements;
    }
    
    

    /////////////////////////////////////////////////////////////////////////
    /////////////////////////////////////////////////////////////////////////
    //// Begin of Experimental Parts!!!
    /////////////////////////////////////////////////////////////////////////
    /////////////////////////////////////////////////////////////////////////
    
    /**
     * Generates BtransCircles without making the Graph chordal.
     * Unfortunatly we didn't either find enough circles or too many circles.
     * This method uses DepthFirstSearch to find small circles first
     * @param topLevelFormula
     * @param vertices
     * @return
     */
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
                btransList.add(ImpliesFormula.create(AndFormula.generate(newList), c));
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
                btransList.add(ImpliesFormula.create(AndFormula.generate(newList), c));
            }
        }
        
        return AndFormula.generate(btransList);
    } // generateBtransCircles

    
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
                            String token =  circle_elem.getEquivalenceName(next_elem);
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
                            String token =  circle_elem.getEquivalenceName(next_elem);
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
    

    

    protected synchronized List<List<PropositionalVariable>> getCircles() {
        return circles;
    }

    protected synchronized void addCircle(List<PropositionalVariable> circle) {
        circlecounter++;
        circles2.add(circle);
        if (circlecounter % 10000 == 0)
            System.out.print(" " + circlecounter);
    }

    protected synchronized void addHashCircle(
            HashSet<PropositionalVariable> circle) {
        if (!hashCircles.contains(circle)) {
            circlecounter++;
            hashCircles.add(circle);
            if (circlecounter % 10000 == 0)
                System.out.print(" " + circlecounter);
        }
    }

    protected synchronized List<GraphReductionThread> getThreads() {
        return threads;
    }

}
