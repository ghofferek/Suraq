/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import org.junit.Assert;

import java.util.*;

public class ResProof{

    public static final int MAX_PROOF_SIZE = 100000;
    public static final int MAX_LIT_NUM    = 10000;

    ResNode root = null;
    int nodeCount = 0;

    ResNode[] nodeRef= new ResNode[MAX_PROOF_SIZE];
    int[] lit_part = new int[MAX_LIT_NUM];

    boolean[] visited= new boolean[MAX_PROOF_SIZE];

    public ResProof(){
        Arrays.fill(nodeRef, null);
        Arrays.fill(lit_part, 0);
    }

    // part for axioms should be 0
    ResNode addLeaf( Collection<Lit> cl, int part ){
        ResNode n = new ResNode(nodeCount, true, cl, null, null, 0, part);
        nodeRef[nodeCount] = n;
        nodeCount++;
        return n;
    }

    // * if cl==null then the clause is computed by applying resolution
    //   on left and right. 
    // * If pivot == 0 then pivot variable is also discovered automatically. 
    // * Node: part for internal node is set to be -1.
    ResNode addIntNode(Collection<Lit> cl,ResNode left,ResNode right,int pivot){
        ResNode n = new ResNode(nodeCount, false, cl, left, right, pivot, -1);
        nodeRef[nodeCount] = n;
        nodeCount++;
        return n;
    }

    void recCheckProof( ResNode n){
        if( visited[n.id] ) return;
        System.out.println( n.id+":"+n.cl);
        visited[n.id] = true;
        if( n.isLeaf ){
            Assert.assertTrue( "Pivot for leaf", n.pivot == 0 );
            Assert.assertTrue( "Parent for leaf", 
                               n.left == null && n.right == null );
        }else{
            Assert.assertTrue( "Parent missing",
                               n.left != null && n.right != null );
            Assert.assertTrue( "pivot litrals are not present",
                              n.left.cl.contains( n.pivot, true) &&
                              n.right.cl.contains( n.pivot, false) );
            Clause c = new Clause(n.left.cl);
            c.rmLit( n.pivot, true );
            c.addAllLit( n.right.cl );
            c.rmLit( n.pivot, false );
            Assert.assertTrue("node is not result of resolution of parents",
                              n.cl.equals(c));
            recCheckProof( n.left  );
            recCheckProof( n.right );
        }
    }

    public void checkProof(){
        Arrays.fill(visited, false);
        recCheckProof(root);
        Assert.assertTrue("Root is not empty clause", root.cl.isEmpty() );
    }

// Start of untested code-----------------------------------------
    void reOrgProof( ResNode n ){
        Lit pl = new Lit( n.pivot, true  );
        Lit nl = new Lit( n.pivot, false );

        while(true){
            if(!n.left.isLeaf) { 
                if(n.cl.contains( n.left.pivot, true))
                    { n.moveParent( true, true ); continue; }
                if(n.cl.contains( n.left.pivot, false)) 
                    { n.moveParent( true, false ); continue; }
            }
            if(!n.right.isLeaf){
                if( n.cl.contains( n.right.pivot, true )) 
                    { n.moveParent( false, true ); continue; }

                if(n.cl.contains( n.right.pivot, false )) 
                    { n.moveParent( false, false ); continue; } 
            }
            break;
        }
        // Check Left
        int goLeft = n.left.checkMovable(pl);
        // Check Right
        int goRight = n.left.checkMovable(nl);

    }

    void recSeparateProof( ResNode n){
        if( visited[n.id] ) return;
        if( n.isLeaf ){ visited[n.id] = true; return; }
        recSeparateProof( n.left  );
        recSeparateProof( n.right );
        visited[n.id] = true;

        // Convert a node into leaf 
        int lp = n.left.part;
        int rp = n.right.part;
        if( lp != -1 && rp != -1 && (lp == rp || lp == 0 || rp == 0) ){
            if( lp == 0 ) n.convertToLeaf(rp); else n.convertToLeaf(lp);
            return;
        }

        if( lit_part[n.pivot] != 0 ){
            reOrgProof(n);
        }
    }
    
    public void separateProof(){
        Arrays.fill(visited, false);        
        recSeparateProof(root);
    }

 //End of untested code-------------------------------------------

    public void test(){
        List<Lit> c1 = Arrays.asList(new Lit(1,true), new Lit(2,false));
        List<Lit> c2 = Arrays.asList(new Lit(1,false) );
        List<Lit> c3 = Arrays.asList(new Lit(2,true));
        ResNode n1 = addLeaf(c1, 1);
        ResNode n2 = addLeaf(c2, 2);
        ResNode n3 = addLeaf(c3, 0);
        ResNode n4 = addIntNode( null, n1, n2, 0);
        root = addIntNode( null, n4, n3, 0);

        checkProof();
    }
}