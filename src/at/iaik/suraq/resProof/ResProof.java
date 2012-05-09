/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import org.junit.Assert;

import java.util.*;

public class ResProof{

    public static final int MAX_PROOF_SIZE = 100000;
    public static final int MAX_LIT_NUM    = 10000;

    public ResNode root = null;
    public int nodeCount = 0;

    public ResNode[] nodeRef= new ResNode[MAX_PROOF_SIZE];
    public int[] var_part = new int[MAX_LIT_NUM];

    public boolean[] visited= new boolean[MAX_PROOF_SIZE];

    public ResProof(){
        Arrays.fill(nodeRef, null);
        Arrays.fill(var_part, 0);
    }

    // part for axioms should be 0
    ResNode addLeaf( Collection<Lit> cl, int part ){
        ResNode n = new ResNode(nodeCount, true, cl, null, null, 0, part);
        //nodeRef[nodeCount] = n;
        nodeCount++;
        return n;
    }

    // * if cl==null then the clause is computed by applying resolution
    //   on left and right. 
    // * If pivot == 0 then pivot variable is also discovered automatically. 
    // * Node: part for internal node is set to be -1.
    ResNode addIntNode(Collection<Lit> cl,ResNode left,ResNode right,int pivot){
        ResNode n = new ResNode(nodeCount, false, cl, left, right, pivot, -1);
        //nodeRef[nodeCount] = n;
        nodeCount++;
        return n;
    }

    void recCheckProof( ResNode n){
        if( visited[n.id] ) return;
        System.out.println(n);
        if( n.isLeaf ){
            Assert.assertTrue( "Pivot for leaf", n.pivot == 0 );
            Assert.assertTrue( "Parent for leaf", 
                               n.left == null && n.right == null );
            Iterator<Lit> iter = n.cl.iterator();
            while(iter.hasNext()){
                Lit l = iter.next();
                if(  var_part[l.var()] != 0 )
                    Assert.assertTrue("a local is in wrong partition",
                                      var_part[l.var()] == n.part );
            }
        }else{
            Assert.assertTrue( "Parent missing",
                               n.left != null && n.right != null );
            Assert.assertTrue( "pivot litrals are not present",
                              n.left.cl.contains( n.pivot, true) &&
                              n.right.cl.contains( n.pivot, false) );
            Clause c = new Clause(n.left.cl,n.right.cl,n.pivot);
            Assert.assertTrue("node is not result of resolution of parents",
                              n.cl.equals(c));
            recCheckProof( n.left  );
            recCheckProof( n.right );
        }
        visited[n.id] = true;
    }

    public void checkProof(){
        Arrays.fill(visited, false);
        recCheckProof(root);
        Assert.assertTrue("Root is not empty clause", root.cl.isEmpty() );
    }

// Start of untested code-----------------------------------------
    void reOrderStep(ResNode n){

        // Convert a node into leaf 
        int lp = n.left.part;
        int rp = n.right.part;
        if( lp != -1 && rp != -1 && (lp == rp || lp == 0 || rp == 0) ){
            if( lp == 0 ) n.convertToLeaf(rp); else n.convertToLeaf(lp);
            return;
        }
        // if pivot is is global then return
        if( var_part[n.pivot] == 0 ) return;

        //Check and fix if parents pivot is in n
        while(true){
            boolean del = false, LeftParent = false, LeftGrandParent = false;
            
            if(!n.left.isLeaf) {
                if(n.cl.contains( n.left.pivot, true)){ 
                    del = true; LeftParent=true; LeftGrandParent=true; 
                } else if(n.cl.contains( n.left.pivot, false)) { 
                    del = true; LeftParent=true; LeftGrandParent=false; 
                }
            }
            if(!del && !n.right.isLeaf){
                if( n.cl.contains( n.right.pivot, true )) { 
                    del = true; LeftParent=false; LeftGrandParent=true; 
                }else if(n.cl.contains( n.right.pivot, false )) { 
                    del = true; LeftParent=false; LeftGrandParent=false; 
                }
            }

            if( del ){
                n.moveParent( LeftParent, LeftGrandParent );
                if( !n.refresh() ) return;
                continue;
            }
            break;
        }

        // push up the local resolution
        Lit pl = new Lit( n.pivot, true  );
        Lit nl = new Lit( n.pivot, false );
        // Check Left
        int goLeft = n.left.checkMovable(pl);
        // Check Right
        int goRight = n.right.checkMovable(nl);
        
        Assert.assertTrue("Both unmovable parent not possible!",
                          goLeft != -1 || goRight != -1 );

        // L = Res(LL, LR), R = Res(RL, RR), N = Res(L,R)
        ResNode L = n.left, R = n.right, n1=null, n2=null;
        ResNode LL = null, LR = null, RL = null, RR = null;
        int piv= n.pivot, Lpiv=0, Rpiv =0;
        if(!L.isLeaf){ LL = L.left; LR = L.right; Lpiv = L.pivot;}
        if(!R.isLeaf){ RL = R.left; RR = R.right; Rpiv = R.pivot;}

        if(goLeft == 2){ // -> N1 = Res(LL,R) N = Res(N1,LR)
            n1 = addIntNode( null, LL, R, piv);
            n.left  = n1;
            n.right = LR;
            n.pivot = Lpiv;
        }else if(goLeft == 3){ // -> N1 = Res(LR,R) N = Res(LL,N1)
            n1 = addIntNode( null, LR, R, piv);
            n.left  = LL;
            n.right = n1;
            n.pivot = Lpiv;
        }else if(goRight == 2){ // -> N1 = Res(L,RL) N = Res(N1,RR)
            n1 = addIntNode( null, L, RL, piv);
            n.left = n1;
            n.right  = RR;
            n.pivot = Rpiv;
        }else if(goRight == 3){ // -> N1 = Res(L,RR) N = Res(RL,N1)
             n1 = addIntNode( null, L, RR, piv);
            n.left  = RL;
            n.right = n1;
            n.pivot = Rpiv;
        }else if(goLeft == 1){//-> N1=Res(LL,R) N2=Res(LR,R) N = Res(N1,N2)
            n1 = addIntNode( null, LL, R, piv);
            n2 = addIntNode( null, LR, R, piv);
            n.left = n1; 
            n.right = n2;
            n.pivot = Lpiv;
        }else if(goRight == 1){//-> N1=Res(L,RL) N2=Res(L,RR) N = Res(N1,N2)
            n1 = addIntNode( null, L, RL, piv);
            n2 = addIntNode( null, L, RR, piv);
            n.left  = n1;
            n.right = n2;
            n.pivot = Rpiv;
        }
        n.left.addChild(n);
        n.right.addChild(n);
        L.rmChildWithCleanUP(n);
        R.rmChildWithCleanUP(n);

        reOrderStep(n1);
        if(n2 != null) reOrderStep(n2);

        if(!n.refresh()) return;
        
    }

    void recDeLocalizeProof( ResNode n){
        if( visited[n.id] ) return;
        if( n.isLeaf ){ visited[n.id] = true; return; }
        recDeLocalizeProof( n.left  );
        recDeLocalizeProof( n.right );
        visited[n.id] = true;

        // Node may get removed in refresh
        if( !n.refresh() ) return;
        
        reOrderStep(n);
    }
    
    public void deLocalizeProof(){
        Arrays.fill(visited, false);        
        recDeLocalizeProof(root);
    }

 //End of untested code-------------------------------------------

}