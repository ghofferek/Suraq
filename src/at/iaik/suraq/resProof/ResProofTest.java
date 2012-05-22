/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */

package at.iaik.suraq.resProof;

import java.util.Arrays;
import java.util.List;

public class ResProofTest {

    private void localizeProof(ResProof prf) {
        prf.checkProof(false);
        prf.rmDoubleLits();
        prf.checkProof(false);
        prf.deLocalizeProof();
        System.out.println("===================");
        prf.checkProof(false);
    }

    public void t1() {
        System.out.println("Example 1=>");
        ResProof prf = new ResProof();
        List<Lit> c1 = Arrays.asList(new Lit(1, true), new Lit(2, false));
        List<Lit> c2 = Arrays.asList(new Lit(1, false));
        List<Lit> c3 = Arrays.asList(new Lit(2, true));
        ResNode n1 = prf.addLeaf(c1, 1);
        ResNode n2 = prf.addLeaf(c2, 2);
        ResNode n3 = prf.addLeaf(c3, 0);
        ResNode n4 = prf.addIntNode(null, n1, n2, 0);
        ResNode n5 = prf.addIntNode(null, n4, n3, 0);

        prf.setRoot(n5);

        prf.checkProof(true);
    }

    public void t2() {
        System.out.println("Example 2=>");

        ResProof prf = new ResProof();

        int g1 = 1;
        int g2 = 2;
        int l = 3;

        List<Lit> c1 = Arrays.asList(new Lit(g1, true));
        List<Lit> c2 = Arrays.asList(new Lit(g1, false), new Lit(l, true));
        List<Lit> c3 = Arrays.asList(new Lit(g2, false), new Lit(l, false));
        List<Lit> c4 = Arrays.asList(new Lit(g2, true));

        prf.var_part[g1] = 0; // global variable
        prf.var_part[g2] = 0; // global variable
        prf.var_part[l] = 2; // partition 2 local variable

        ResNode n1 = prf.addLeaf(c1, 1);
        ResNode n2 = prf.addLeaf(c2, 2);
        ResNode n3 = prf.addLeaf(c3, 2);
        ResNode n4 = prf.addLeaf(c4, 3);

        ResNode i1 = prf.addIntNode(null, n1, n2, g1);
        ResNode i2 = prf.addIntNode(null, n3, n4, g2);
        ResNode i3 = prf.addIntNode(null, i1, i2, l);

        prf.setRoot(i3);

        localizeProof(prf);

    }

    public void t3(boolean b) {
        ResProof prf = new ResProof();
        System.out.println("Example 3=>" + b);

        boolean T = b;
        boolean F = !b;

        int l = 1;
        int g1 = 2;
        int g2 = 3;
        int g3 = 4;

        prf.var_part[l] = 1;
        prf.var_part[g1] = 0;
        prf.var_part[g2] = 0;
        prf.var_part[g3] = 0;

        List<Lit> c1 = Arrays.asList(new Lit(g1, T), new Lit(l, T));
        List<Lit> c2 = Arrays.asList(new Lit(g1, F));
        List<Lit> c3 = Arrays.asList(new Lit(g1, T), new Lit(g2, F), new Lit(l,
                F));
        List<Lit> c4 = Arrays.asList(new Lit(g3, T), new Lit(g2, T));
        List<Lit> c5 = Arrays.asList(new Lit(l, F), new Lit(g3, F));

        ResNode n1 = prf.addLeaf(c1, 1);
        ResNode n2 = prf.addLeaf(c2, 2);
        ResNode n3 = prf.addLeaf(c3, 1);
        ResNode n4 = prf.addLeaf(c4, 3);
        ResNode n5 = prf.addLeaf(c5, 1);

        ResNode i1 = prf.addIntNode(null, n1, n2, g1);
        ResNode i2 = prf.addIntNode(null, n4, n5, g3);
        ResNode i3 = prf.addIntNode(null, n3, i2, g2);
        ResNode i4 = prf.addIntNode(null, i1, i3, l);
        ResNode i5 = prf.addIntNode(null, i4, n2, g1);

        prf.setRoot(i5);

        localizeProof(prf);
    }

    public void t4() {
        ResProof prf = new ResProof();
        prf.loadProof();
        localizeProof(prf); 
    }    

    public void test() {
        t4();
        // System.out.println("----------------------------------------------");
        // t1();
        // System.out.println("----------------------------------------------");
        // t2();
        // System.out.println("----------------------------------------------");
        // t3(true);
        // System.out.println("----------------------------------------------");
        // t3(false);
    }
}
