/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */

package at.iaik.suraq.resProof;

import org.junit.Assert;

import java.util.*;

public class ResProofTest{

    public ResProofTest(){

    }

    public void test(){
        ResProof prf = new ResProof();
        List<Lit> c1 = Arrays.asList(new Lit(1,true), new Lit(2,false));
        List<Lit> c2 = Arrays.asList(new Lit(1,false) );
        List<Lit> c3 = Arrays.asList(new Lit(2,true));
        ResNode n1 = prf.addLeaf(c1, 1);
        ResNode n2 = prf.addLeaf(c2, 2);
        ResNode n3 = prf.addLeaf(c3, 0);
        ResNode n4 = prf.addIntNode( null, n1, n2, 0);
        prf.root = prf.addIntNode( null, n4, n3, 0);

        prf.deLocalizeProof();        
        prf.checkProof();
    }
}
