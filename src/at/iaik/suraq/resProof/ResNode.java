/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;

import org.junit.Assert;

public class ResNode {

    public int id = 0;
    public boolean isLeaf = true;

    public Clause cl = null;
    public int pivot = 0;
    public int part = 0;

    public ResNode left = null;
    public ResNode right = null;
    public HashSet<Integer> children = new HashSet<Integer>();

    public ResNode(int pId, boolean pIsLeaf) {
        id = pId;
        cl = new Clause();
        isLeaf = pIsLeaf;
    }

    public ResNode(int pId, boolean pIsLeaf, Collection<Lit> pCl,
            ResNode pLeft, ResNode pRight, int pPivot, int pPart) {
        id = pId;
        isLeaf = pIsLeaf;
        part = pPart;

        if (pIsLeaf) {
            cl = new Clause(pCl);
            return;
        }

        boolean isLeftPos = true;

        if (pPivot == 0) {
            Iterator<Lit> itr = pLeft.cl.iterator();
            while (itr.hasNext()) {
                Lit l = itr.next();
                if (pRight.cl.contains(l.negLit())) {
                    pPivot = l.var();
                    isLeftPos = l.isPos();
                    break;
                }
            }
            Assert.assertTrue("pivot not found!", pPivot != 0);
        }
        pivot = pPivot;

        if (pCl == null) {
            cl = new Clause(pLeft.cl);
            cl.rmLit(pivot, isLeftPos);
            cl.addAllLit(pRight.cl);
            cl.rmLit(pivot, !isLeftPos);
        } else {
            cl = new Clause(pCl);
        }

        if (isLeftPos) {
            left = pLeft;
            right = pRight;
        } else {
            left = pRight;
            right = pLeft;
        }

        left.addChild(this);
        right.addChild(this);
    }

    public void rmChild(ResNode n) {
        Assert.assertTrue("Removing non-existant child",
                children.contains(n.id));
        children.remove(n.id);
        // TODO: if( chidren.isEmpty() ) delete the node from nodeRef
    }

    public void addChild(ResNode n) {
        Assert.assertTrue("Adding existing child", !children.contains(n.id));
        children.add(n.id);
    }

    public void convertToLeaf(int pPart) {
        isLeaf = true;
        part = pPart;
        left.rmChild(this);
        right.rmChild(this);
        left = null;
        right = null;
        pivot = 0;
    }

    public int checkMovable(Lit l) {
        int goLeft = -1;
        if (part != -1) {
            // Assert.assertTrue("n.pivot is not from n.left partition",
            // n.left.part == lit_part[n.pivot] );
            return -1; // move disallowed
        }
        boolean ll = left.cl.contains(l);
        boolean lr = right.cl.contains(l);
        if (ll && lr)
            return 1; // both parents have l
        if (ll)
            return 2; // left parent have l
        if (lr)
            return 3; // right parent have l
        Assert.assertTrue("l is not in any parent", false);
        return 0;
    }

    public void moveParent(boolean LeftParent, boolean LeftGrandParent) {

        ResNode looser = null;
        ResNode gainer = null;

        if (LeftParent)
            looser = left;
        else
            looser = right;
        if (LeftGrandParent)
            gainer = looser.left;
        else
            gainer = looser.right;
        if (LeftParent)
            left = gainer;
        else
            right = gainer;

        looser.rmChild(this);
        gainer.addChild(this);
    }

}
