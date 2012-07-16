/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;

public class ResNode {

    public int id = 0;
    public boolean isLeaf = true;

    public Clause cl = null;
    public int pivot = 0;
    public int part = 0;

    public ResNode left = null;
    public ResNode right = null;
    public HashSet<ResNode> children = new HashSet<ResNode>();

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

        assert (pLeft != null && pRight != null); // "At least a parent is missing!",

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
            assert (pPivot != 0); // "pivot not found!",
        } else {
            if (pLeft.cl.contains(pPivot, true)
                    && pRight.cl.contains(pPivot, false)) {
                isLeftPos = true;
            } else if (pRight.cl.contains(pPivot, true)
                    && pLeft.cl.contains(pPivot, false)) {
                isLeftPos = false;
            } else {
                assert (pPivot != 0);// "Parents do not contain lietrals of pivot!",
            }
        }
        pivot = pPivot;

        if (isLeftPos) {
            left = pLeft;
            right = pRight;
        } else {
            left = pRight;
            right = pLeft;
        }

        if (pCl == null) {
            cl = new Clause(left.cl, right.cl, pivot);
        } else {
            cl = new Clause(pCl);
            // TODO: check if cl is result of the resolution!
        }

        left.addChild(this);
        right.addChild(this);
    }

    public void cleanUP() {
        if (!isLeaf && children.isEmpty()) {
            left.rmChild(this);
            left.cleanUP();
            left = null;
            right.rmChild(this);
            right.cleanUP();
            right = null;
            cl.clear();
            // this is ready for garbage collection.
        }
    }

    public void rmChild(ResNode n) {
        assert (children.contains(n));// "Removing non-existant child",
        children.remove(n);
    }

    public void rmChildWithCleanUP(ResNode n) {
        rmChild(n);
        cleanUP();
    }

    public void addChild(ResNode n) {
        assert (!children.contains(n));// "Adding existing child",
        children.add(n);
    }

    public void convertToLeaf(int pPart) {
        isLeaf = true;
        part = pPart;
        left.rmChildWithCleanUP(this);
        right.rmChildWithCleanUP(this);
        left = null;
        right = null;
        pivot = 0;
    }

    public int checkMovable(Lit l) {
        if (isLeaf || part != -1)
            return -1; // move disallowed
        boolean ll = left.cl.contains(l);
        boolean lr = right.cl.contains(l);
        if (ll && lr)
            return 1; // both parents have l
        if (ll)
            return 2; // left parent have l
        if (lr)
            return 3; // right parent have l
        assert (false);// "l is not in any parent",
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

        gainer.addChild(this);
        looser.rmChildWithCleanUP(this);
    }

    public void moveChidren(boolean toLeftParent) {
        ResNode gainer = null;
        if (toLeftParent)
            gainer = left;
        else
            gainer = right;

        Iterator<ResNode> itr = children.iterator();
        while (itr.hasNext()) {
            ResNode n = itr.next();
            if (n.left == this)
                n.left = gainer;
            else
                n.right = gainer;
            gainer.addChild(n);
        }

        children.clear();
        cleanUP();
    }

    public boolean refresh() {

        if (!left.cl.contains(pivot, true)) {
            moveChidren(true);
            return false; // Node is dead
        }
        if (!right.cl.contains(pivot, false)) {
            moveChidren(false);
            return false; // Node is dead
        }
        cl = new Clause(left.cl, right.cl, pivot);
        return true; // Node is still valid
    }

    public void print() {
        System.out.println("------------------------------------");
        if (isLeaf)
            System.out.println(id + "> (leaf) part:" + part);
        else
            System.out.println(id + "> left:" + left.id + " right:" + right.id
                    + " pivot:" + pivot);
        System.out.println("Clause: " + cl);
        Iterator<ResNode> itr = children.iterator();
        System.out.print("Chidren: [");
        while (itr.hasNext()) {
            ResNode n = itr.next();
            System.out.print(n.id + ",");
        }
        System.out.println("]");
    }

    @Override
    public String toString() {
        if (isLeaf)
            return id + ":" + cl + " (p" + part + ")";
        else if (part != -1)
            return id + ":" + cl + " l:" + left.id + " r:" + right.id + " piv:"
                    + pivot + " (p" + part + ")";
        else
            return id + ":" + cl + " l:" + left.id + " r:" + right.id + " piv:"
                    + pivot;
    }
}
