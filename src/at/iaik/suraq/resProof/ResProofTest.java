/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */

package at.iaik.suraq.resProof;

import java.util.Arrays;
import java.util.List;

public class ResProofTest {

    @SuppressWarnings("unused")
    private void localizeProof(ResProof prf) {
        prf.computeVitals();
        prf.checkProof(true);
        prf.rmDoubleLits();
        prf.deLocalizeProof();
        prf.computeVitals();
        prf.checkProof(false);
    }

    public void t1() {
        System.out.println("Example 1=>");
        ResProof prf = new ResProof();

        prf.putVarPart(1, 0);
        prf.putVarPart(2, 0);

        List<Literal> c1lits = Arrays.asList(Literal.create(1, true),
                Literal.create(2, false));
        List<Literal> c2lits = Arrays.asList(Literal.create(1, false));
        List<Literal> c3lits = Arrays.asList(Literal.create(2, true));
        Clause c1 = new Clause(c1lits);
        Clause c2 = new Clause(c2lits);
        Clause c3 = new Clause(c3lits);
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

        List<Literal> c1lits = Arrays.asList(Literal.create(g1, true));
        List<Literal> c2lits = Arrays.asList(Literal.create(g1, false),
                Literal.create(l, true));
        List<Literal> c3lits = Arrays.asList(Literal.create(g2, false),
                Literal.create(l, false));
        List<Literal> c4lits = Arrays.asList(Literal.create(g2, true));

        Clause c1 = new Clause(c1lits);
        Clause c2 = new Clause(c2lits);
        Clause c3 = new Clause(c3lits);
        Clause c4 = new Clause(c4lits);

        prf.putVarPart(g1, 0); // global variable
        prf.putVarPart(g2, 0); // global variable
        prf.putVarPart(l, 2); // partition 2 local variable

        ResNode n1 = prf.addLeaf(c1, 1);
        ResNode n2 = prf.addLeaf(c2, 2);
        ResNode n3 = prf.addLeaf(c3, 2);
        ResNode n4 = prf.addLeaf(c4, 3);

        ResNode i1 = prf.addIntNode(null, n1, n2, g1);
        ResNode i2 = prf.addIntNode(null, n3, n4, g2);
        ResNode i3 = prf.addIntNode(null, i1, i2, l);

        prf.setRoot(i3);

        prf.makeLocalFirst(true, true, false);

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

        prf.putVarPart(l, 1);
        prf.putVarPart(g1, 0);
        prf.putVarPart(g2, 0);
        prf.putVarPart(g3, 0);

        List<Literal> c1lits = Arrays.asList(Literal.create(g1, T),
                Literal.create(l, T));
        List<Literal> c2lits = Arrays.asList(Literal.create(g1, F));
        List<Literal> c3lits = Arrays.asList(Literal.create(g1, T),
                Literal.create(g2, F), Literal.create(l, F));
        List<Literal> c4lits = Arrays.asList(Literal.create(g3, T),
                Literal.create(g2, T));
        List<Literal> c5lits = Arrays.asList(Literal.create(l, F),
                Literal.create(g3, F));

        Clause c1 = new Clause(c1lits);
        Clause c2 = new Clause(c2lits);
        Clause c3 = new Clause(c3lits);
        Clause c4 = new Clause(c4lits);
        Clause c5 = new Clause(c5lits);

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

        prf.makeLocalFirst(true, true, false);

    }

    public void t4() {
        System.out.println("Example 4=>(with no printing)");
        ResProof prf = new ResProof();
        prf.loadProof("rsc/test/t4.resProof");
        prf.makeLocalFirst(true, false, false);
    }

    public void test() {
        System.out.println("----------------------------------------------");
        t1();
        System.out.println("----------------------------------------------");
        t2();
        System.out.println("----------------------------------------------");
        t3(true);
        System.out.println("----------------------------------------------");
        t3(false);
        System.out.println("----------------------------------------------");
        t4();
    }

    public boolean takeControl() {
        boolean b = false;
        // true;
        if (b)
            test();
        return b;
    }

    public static void main(String[] args) {
        ResProofTest test = new ResProofTest();
        test.test();
    }
}
