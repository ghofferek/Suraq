/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;

import org.junit.Assert;

public class ResProof {

    public static final int MAX_PROOF_SIZE = 100000;
    public static final int MAX_LIT_NUM = 10000;

    /* Essential fields */
    public ResNode root = null;
    public int nodeCount = 1;
    public int[] var_part = new int[MAX_LIT_NUM];
    public boolean[] visited = new boolean[MAX_PROOF_SIZE];

    /* Proof vital */
    public boolean vitalInfoFresh = false;
    public ResNode[] nodeRef = new ResNode[MAX_PROOF_SIZE];
    public int numberOfNodes;
    public HashSet<ResNode> leaves = new HashSet<ResNode>();

    /* config fields */
    public boolean printWhileChecking = false;

    public ResProof() {
        root = new ResNode(0, false);
        Arrays.fill(nodeRef, null);
        Arrays.fill(var_part, -1);
    }

    // part for axioms should be 0
    public ResNode addLeaf(Collection<Lit> cl, int part) {
        assert (!vitalInfoFresh);
        ResNode n = new ResNode(nodeCount, true, cl, null, null, 0, part);
        incNodeCount(n);
        return n;
    }

    // * if cl==null then the clause is computed by applying resolution
    // on left and right.
    // * If pivot == 0 then pivot variable is also discovered automatically.
    // * Node: part for internal node is set to be -1.
    public ResNode addIntNode(Collection<Lit> cl, ResNode left, ResNode right,
            int pivot) {
        assert (!vitalInfoFresh);
        ResNode n = new ResNode(nodeCount, false, cl, left, right, pivot, -1);
        incNodeCount(n);
        return n;
    }

    private void incNodeCount(ResNode n) {
        // nodeRef[nodeCount] = n;
        nodeCount++;
        Assert.assertTrue("Maximum capacity of proof size reached!",
                nodeCount < MAX_PROOF_SIZE);
    }

    public void setRoot(ResNode n) {
        assert (!vitalInfoFresh);
        root.left = n;
        n.addChild(root);
    }

    public ResNode getRoot() {
        return root.left;
    }

    /*
     * vital computation
     */
    public void disruptVitals() {
        vitalInfoFresh = false;
        Arrays.fill(nodeRef, null);
        numberOfNodes = 0;
        leaves.clear();
    }

    public void recComputeVitals(ResNode n) {
        if (visited[n.id])
            return;
        numberOfNodes++;
        nodeRef[n.id] = n;
        if (n.isLeaf) {
            leaves.add(n);
        } else {
            recComputeVitals(n.left);
            recComputeVitals(n.right);
        }
        visited[n.id] = true;
    }

    public void computeVitals() {
        disruptVitals();
        Arrays.fill(visited, false);
        ResNode root = getRoot();
        if (root != null)
            recComputeVitals(root);
        vitalInfoFresh = true;
    }

    /*
     * Dumping/loading the proofs in a file
     */
    void recDumpProof(BufferedWriter wr, ResNode n) throws IOException {
        if (visited[n.id])
            return;
        if (n.isLeaf) {
            wr.write(String.valueOf(n.id));
            wr.write(" ");
            wr.write(String.valueOf(n.pivot));
            wr.write(" ");
            wr.write(String.valueOf(n.part));
            wr.write(" ");
            Iterator<Lit> iter = n.cl.iterator();
            while (iter.hasNext()) {
                Lit l = iter.next();
                wr.write(String.valueOf(l.l));
                wr.write(" ");
            }
        } else {
            recDumpProof(wr, n.left);
            recDumpProof(wr, n.right);
            wr.write(String.valueOf(n.id));
            wr.write(" ");
            wr.write(String.valueOf(n.pivot));
            wr.write(" ");
            wr.write(String.valueOf(n.left.id));
            wr.write(" ");
            wr.write(String.valueOf(n.right.id));
            wr.write(" ");
        }
        wr.write("\n");
        visited[n.id] = true;
    }

    public void dumpProof(String file) {
        // String file = "tmp/test.res";
        Arrays.fill(visited, false);
        try {
            // create FileOutputStream object
            File fl = new File(file);
            FileWriter fs = new FileWriter(fl);
            BufferedWriter wr = new BufferedWriter(fs);
            for (int v = 1; var_part[v] != -1; v++) {
                wr.write(String.valueOf(v));
                wr.write(" ");
                wr.write(String.valueOf(var_part[v]));
                wr.write("\n");
            }
            wr.write(String.valueOf(0));
            wr.write("\n");
            recDumpProof(wr, getRoot());
            wr.write(String.valueOf(0));
            wr.write("\n");
            // int v = 123;
            // wr.write(String.valueOf(v));
            wr.close();

        } catch (IOException e) {
            System.out.println("IOException : " + e);
        }

    }

    public void loadProof(String file) {
        // String file = "tmp/test.res";
        try {
            // create FileOutputStream object
            File fl = new File(file);
            FileReader fs = new FileReader(fl);
            BufferedReader rd = new BufferedReader(fs);

            String rdLine;

            while ((rdLine = rd.readLine()) != null) {
                String[] is = rdLine.split(" ");
                int v = Integer.parseInt(is[0]);
                if (v == 0)
                    break;
                Assert.assertTrue("var and only parts should be there",
                        is.length == 2);
                var_part[v] = Integer.parseInt(is[1]);
            }
            ResNode n = null;
            while ((rdLine = rd.readLine()) != null) {
                String[] is = rdLine.split(" ");
                int id = Integer.parseInt(is[0]);
                if (id == 0)
                    break;
                int piv = Integer.parseInt(is[1]);
                if (piv == 0) {
                    int part = Integer.parseInt(is[2]);
                    Clause cl = new Clause();
                    for (int i = 3; i < is.length; i++) {
                        Lit l = new Lit(Integer.parseInt(is[i]));
                        cl.addLit(l);
                    }
                    n = addLeaf(cl, part);
                } else {
                    int lid = Integer.parseInt(is[2]);
                    int rid = Integer.parseInt(is[3]);
                    n = addIntNode(null, nodeRef[lid], nodeRef[rid], piv);
                }
                nodeRef[id] = n;
            }
            setRoot(n);
            rd.close();
        } catch (IOException e) {
            System.out.println("IOException : " + e);
        }

    }

    /*
     * Checking Proof correctness
     */

    void recCheckProof(ResNode n) {
        if (visited[n.id])
            return;
        if (printWhileChecking)
            System.out.println(n);
        // Todo: Check double lits issue if disabled globally
        if (n.isLeaf) {
            Assert.assertTrue("Pivot at leaf!", n.pivot == 0);
            Assert.assertTrue("Parent of a leaf!", n.left == null
                    && n.right == null);
            Iterator<Lit> iter = n.cl.iterator();
            while (iter.hasNext()) {
                Lit l = iter.next();
                Assert.assertTrue("an local with uninitialized partition",
                        var_part[l.var()] != -1);
                if (var_part[l.var()] != 0)
                    Assert.assertTrue("a local is in wrong partition!",
                            var_part[l.var()] == n.part);
            }
        } else {
            Assert.assertTrue("A parent missing!", n.left != null
                    && n.right != null);
            Assert.assertTrue(
                    "pivot litrals are not present in parents!",
                    n.left.cl.contains(n.pivot, true)
                            && n.right.cl.contains(n.pivot, false));
            Clause c = new Clause(n.left.cl, n.right.cl, n.pivot);
            Assert.assertTrue(
                    "node is not the result of resolution of parents",
                    n.cl.equals(c));
            recCheckProof(n.left);
            recCheckProof(n.right);
        }
        visited[n.id] = true;
    }

    public void checkProof(boolean doPrint) {
        printWhileChecking = doPrint;
        if (printWhileChecking) {
            System.out.println("============== Checking Proof ============");
            if (vitalInfoFresh) {
                System.out.println("Number of nodes  = " + numberOfNodes);
                System.out.println("Number of leaves = " + leaves.size());
            } else {
                System.out.println("Number of active nodes" + "<" + nodeCount);
            }
            System.out.print("var partitions:");
            for (int v = 1; var_part[v] != -1; v++)
                System.out.print(" " + v + ":p" + var_part[v]);
            System.out.println("\n==========================================");
        }
        Arrays.fill(visited, false);
        ResNode root = getRoot();
        if (root != null) {
            recCheckProof(root);
            Assert.assertTrue("Root is not empty clause", root.cl.isEmpty());
        }
        if (printWhileChecking)
            System.out.println("==========================================");
    }

    // Start : remove double literals

    void recRmDoubleLits(ResNode n) {
        if (visited[n.id])
            return;
        if (n.isLeaf) {
            visited[n.id] = true;
            return;
        }

        recRmDoubleLits(n.left);
        recRmDoubleLits(n.right);
        visited[n.id] = true;
        // Node may get removed in refresh
        if (!n.refresh())
            return;

        if (n.cl.contains(n.pivot, true)) {
            n.moveChidren(true);
        } else if (n.cl.contains(n.pivot, false)) {
            n.moveChidren(false);
        }
    }

    public void rmDoubleLits() {
        disruptVitals();
        Arrays.fill(visited, false);
        recRmDoubleLits(getRoot());
    }

    // boolean p=false;
    // Start : Proof restructuring-----------------------------------------
    void reOrderStep(ResNode n) {
        // if(n.id==3001) p =true;
        // if(n.id==6432){
        // System.out.println(n);
        // System.out.println(n.left);
        // // System.out.println(n.left.left);
        // // System.out.println(n.left.right);
        // System.out.println(n.right);
        // }
        // if(p) System.out.println(n);

        boolean mv = false;
        do {
            // If a node is derived form both parents
            // that are "local" or "global axiom"
            // then convert the node into a local node by
            // setting n.part
            //
            // n.part == 0 -> axiom or only derived from axioms
            // n.part == -1 -> derived from clauses of different parts
            // n.part > 0 -> derived from a single part or global axioms
            int lp = n.left.part;
            int rp = n.right.part;
            if (lp != -1 && rp != -1 && (lp == rp || lp == 0 || rp == 0)) {
                int np = 0;
                if (lp == 0)
                    np = rp;
                else
                    np = lp;
                n.part = np;
                return;
            }
            // if pivot is global then return
            if (var_part[n.pivot] == 0)
                return;

            // Check and fix if parents pivot is in n
            mv = false;
            boolean LeftParent = false, LeftGrandParent = false;
            // Note: the following condition only checks the partition.
            // If the parent is derived from a single partition then
            // we will not move in the direction and dont worry about it.
            if (n.left.part == -1) {
                if (n.cl.contains(n.left.pivot, true)) {
                    mv = true;
                    LeftParent = true;
                    LeftGrandParent = true;
                } else if (n.cl.contains(n.left.pivot, false)) {
                    mv = true;
                    LeftParent = true;
                    LeftGrandParent = false;
                }
            }

            if (!mv && n.right.part == -1) {
                if (n.cl.contains(n.right.pivot, true)) {
                    mv = true;
                    LeftParent = false;
                    LeftGrandParent = true;
                } else if (n.cl.contains(n.right.pivot, false)) {
                    mv = true;
                    LeftParent = false;
                    LeftGrandParent = false;
                }
            }

            if (mv) {
                n.moveParent(LeftParent, LeftGrandParent);
                if (!n.refresh())
                    return;
            }
        } while (mv);

        // move up the local resolution
        Lit pl = new Lit(n.pivot, true);
        Lit nl = new Lit(n.pivot, false);
        // Check Left
        int goLeft = n.left.checkMovable(pl);
        // Check Right
        int goRight = n.right.checkMovable(nl);
        // System.out.println("Moving a node!"+n);

        Assert.assertTrue(n + ":Both unmovable parents is not possible!",
                goLeft != -1 || goRight != -1);

        // L = Res(LL, LR), R = Res(RL, RR), N = Res(L,R)
        ResNode L = n.left, R = n.right, n1 = null, n2 = null;
        ResNode LL = null, LR = null, RL = null, RR = null;
        int piv = n.pivot, Lpiv = 0, Rpiv = 0;
        if (L.part == -1) {
            LL = L.left;
            LR = L.right;
            Lpiv = L.pivot;
        }
        if (R.part == -1) {
            RL = R.left;
            RR = R.right;
            Rpiv = R.pivot;
        }

        if (goLeft == 2) { // -> N1 = Res(LL,R) N = Res(N1,LR)
            n1 = addIntNode(null, LL, R, piv);
            n.left = n1;
            n.right = LR;
            n.pivot = Lpiv;
        } else if (goLeft == 3) { // -> N1 = Res(LR,R) N = Res(LL,N1)
            n1 = addIntNode(null, LR, R, piv);
            n.left = LL;
            n.right = n1;
            n.pivot = Lpiv;
        } else if (goRight == 2) { // -> N1 = Res(L,RL) N = Res(N1,RR)
            n1 = addIntNode(null, L, RL, piv);
            n.left = n1;
            n.right = RR;
            n.pivot = Rpiv;
        } else if (goRight == 3) { // -> N1 = Res(L,RR) N = Res(RL,N1)
            n1 = addIntNode(null, L, RR, piv);
            n.left = RL;
            n.right = n1;
            n.pivot = Rpiv;
        } else if (goLeft == 1) {// -> N1=Res(LL,R) N2=Res(LR,R) N = Res(N1,N2)
            n1 = addIntNode(null, LL, R, piv);
            n2 = addIntNode(null, LR, R, piv);
            n.left = n1;
            n.right = n2;
            n.pivot = Lpiv;
        } else if (goRight == 1) {// -> N1=Res(L,RL) N2=Res(L,RR) N = Res(N1,N2)
            n1 = addIntNode(null, L, RL, piv);
            n2 = addIntNode(null, L, RR, piv);
            n.left = n1;
            n.right = n2;
            n.pivot = Rpiv;
        }
        n.left.addChild(n);
        n.right.addChild(n);
        L.rmChildWithCleanUP(n);
        R.rmChildWithCleanUP(n);

        reOrderStep(n1);
        if (n2 != null)
            reOrderStep(n2);

        if (!n.refresh())
            return;

    }

    void recDeLocalizeProof(ResNode n) {
        if (visited[n.id])
            return;
        if (n.isLeaf || n.part != -1) {
            visited[n.id] = true;
            return;
        }
        recDeLocalizeProof(n.left);
        recDeLocalizeProof(n.right);
        visited[n.id] = true;

        // Node may get removed in refresh
        if (!n.refresh())
            return;

        reOrderStep(n);
    }

    public void deLocalizeProof() {
        disruptVitals();
        Arrays.fill(visited, false);
        recDeLocalizeProof(getRoot());
    }

    public void localFirstProofs(boolean verify, boolean print, boolean dump) {

        HashSet<ResNode> oldLeaves = null;
        if (verify) {
            computeVitals();
            checkProof(print);
            oldLeaves = new HashSet<ResNode>(leaves);
        }
        if (dump)
            dumpProof("tmp/test.res");
        rmDoubleLits();
        deLocalizeProof();
        if (verify) {
            computeVitals();
            checkProof(print);
            assert (oldLeaves.containsAll(leaves));
        }
    }

    public void tranformResProofs() {
        localFirstProofs(false, false, false);
    }
    // End : Proof restructuring-----------------------------------------

}