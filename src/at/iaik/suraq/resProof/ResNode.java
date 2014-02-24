/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class ResNode implements Comparable<ResNode> {

    /**
     * The id of this node.
     */
    public final int id;

    /**
     * The clause of this node
     */
    private Clause clause;

    /**
     * The pivot of this resolution step, or 0 if this is a leaf.
     */
    private int pivot = 0;

    /**
     * The partition of this node.
     */
    private int part = 0;

    /**
     * The left child. Contains the pivot in positive polarity.
     */
    private ResNode left = null;

    /**
     * The right child. Contains the pivot in negative polarity.
     */
    private ResNode right = null;

    /**
     * This used to be called "children". Working hypothesis is that it actually
     * means parents.
     */
    public final Set<ResNode> parents = new TreeSet<ResNode>();

    /**
     * 
     * Constructs a new <code>ResNode</code>.
     * 
     * @param id
     */
    public ResNode(int id) {
        // if (id == 1991555)
        // assert (id == 1991555);
        this.id = id;
        this.clause = new Clause();
    }

    /**
     * 
     * Constructs a new <code>ResNode</code>.
     * 
     * @param id
     * @param clause
     * @param left
     * @param right
     * @param pivot
     * @param part
     */
    public ResNode(int id, Clause clause, ResNode left, ResNode right,
            int pivot, int part) {
        // if (id == 1991555)
        // assert (id == 1991555);
        this.id = id;
        this.part = part;

        if (left == null && right == null) {
            assert (clause != null);
            this.clause = new Clause(clause);
            return;
        }

        assert (left != null && right != null); // "At least a parent is missing!",

        boolean isLeftPos = true;

        if (pivot == 0) {
            Iterator<Literal> itr = left.clause.iterator();
            while (itr.hasNext()) {
                Literal lit = itr.next();
                if (right.clause.contains(lit.negate())) {
                    pivot = lit.id();
                    isLeftPos = lit.isPos();
                    break;
                }
            }
            assert (pivot != 0); // "pivot not found!",
        } else {
            if (left.clause.contains(pivot, true)
                    && right.clause.contains(pivot, false)) {
                isLeftPos = true;
            } else if (right.clause.contains(pivot, true)
                    && left.clause.contains(pivot, false)) {
                isLeftPos = false;
            } else {
                assert (false);// "Parents do not contain literals of pivot!",
            }
        }
        this.pivot = pivot;

        if (isLeftPos) {
            this.left = left;
            this.right = right;
        } else {
            this.left = right;
            this.right = left;
        }

        if (clause == null) {
            this.clause = new Clause(this.left.clause, this.right.clause,
                    this.pivot);
        } else {
            // check if clause is result of the resolution!
            assert (!clause.contains(pivot, true));
            assert (!clause.contains(pivot, false));
            for (Literal lit : this.left.clause) {
                if (lit.id() != pivot)
                    assert (clause.contains(lit));
            }
            for (Literal lit : this.right.clause) {
                if (lit.id() != pivot)
                    assert (clause.contains(lit));
            }
            for (Literal lit : clause) {
                assert (this.left.clause.contains(lit) || this.right.clause
                        .contains(lit));
            }
            this.clause = new Clause(clause);
        }

        this.left.addParent(this);
        this.right.addParent(this);
    }

    /**
     * Not sure what this does exactly. Seems to remove unreachable nodes.
     */
    public void cleanUp() {
        if (!isLeaf() && parents.isEmpty()) {
            ResNode oldLeft = this.left;
            this.left = null;
            ResNode oldRight = this.right;
            this.right = null;
            oldLeft.removeParent(this);
            oldLeft.cleanUp();
            if (oldLeft != oldRight) {
                oldRight.removeParent(this);
                oldRight.cleanUp();
            }
            // clause.clear();
            // this is ready for garbage collection.
        }
    }

    /**
     * Removes the given node from the set of parents.
     * 
     * @param node
     */
    public void removeParent(ResNode node) {
        assert (node.left != this && node.right != this);
        assert (parents.contains(node));// "Removing non-existent child",
        parents.remove(node);
    }

    /**
     * Removes the given node from the set of parents and performs clean up.
     * 
     * @param n
     */
    public void rmParentWithCleanUp(ResNode n) {
        removeParent(n);
        cleanUp();
    }

    /**
     * Adds the given node to the set of parents.
     * 
     * @param n
     */
    public void addParent(ResNode n) {
        parents.add(n);
    }

    /**
     * Converts this node into a leaf of the given partition.
     * 
     * @param part
     */
    public void convertToLeaf(int part) {
        this.part = part;
        ResNode oldLeft = this.left;
        ResNode oldRight = this.right;
        this.left = null;
        this.right = null;
        oldLeft.rmParentWithCleanUp(this);
        oldRight.rmParentWithCleanUp(this);
        this.pivot = 0;
    }

    /**
     * Fails if this is not a leaf and none of the children has lit.
     * 
     * @param lit
     * @return -1 if move is disallowed, 1 if both children have lit, 2 if left
     *         child has lit, 3 if right child has lit.
     */
    public int checkMovable(Literal lit) {
        if (isLeaf() || part != -1)
            return -1; // move disallowed
        boolean ll = left.clause.contains(lit);
        boolean lr = right.clause.contains(lit);
        if (ll && lr)
            return 1; // both children have lit
        if (ll)
            return 2; // left child has lit
        if (lr)
            return 3; // right children has lit
        assert (false);// "lit is not in any child",
        return 0;
    }

    /**
     * Moves a grandchild to a child position.
     * 
     * @param leftChild
     *            if <code>true</code> take left child
     * @param leftGrandChild
     *            if <code>take</code> left child of child specified by
     *            <code>leftChild</code>
     */
    public void moveChild(boolean leftChild, boolean leftGrandChild) {

        ResNode looser = null;
        ResNode gainer = null;

        if (leftChild)
            looser = left;
        else
            looser = right;
        assert (looser != null);
        if (leftGrandChild)
            gainer = looser.left;
        else
            gainer = looser.right;
        assert (gainer != null);
        if (leftChild)
            left = gainer;
        else
            right = gainer;

        gainer.addParent(this);
        looser.rmParentWithCleanUp(this);
    }

    /**
     * Moves the parents of this node to one of its children.
     * 
     * @param toLeftChild
     *            if <code>true</code> move parents to left child.
     */
    public void moveParents(boolean toLeftChild) {
        ResNode gainer = null;
        if (toLeftChild)
            gainer = left;
        else
            gainer = right;
        assert (gainer != null);
        Iterator<ResNode> itr = parents.iterator();
        while (itr.hasNext()) {
            ResNode parent = itr.next();
            assert (parent.left == this || parent.right == this);
            if (parent.left == this)
                parent.left = gainer;
            else
                parent.right = gainer;
            gainer.addParent(parent);
        }

        parents.clear();
        cleanUp();
    }

    /**
     * Checks whether this node has become obsolete, and if not recomputes its
     * clause.
     * 
     * @return <code>true</code> iff this node is still alive.
     */
    public boolean refresh() {

        if (!left.clause.contains(pivot, true)) {
            moveParents(true);
            return false; // Node is dead
        }
        if (!right.clause.contains(pivot, false)) {
            moveParents(false);
            return false; // Node is dead
        }
        clause = new Clause(left.clause, right.clause, pivot);
        return true; // Node is still valid
    }

    /**
     * 
     * @return the clause of this node
     */
    public Clause getClause() {
        return clause;
    }

    /**
     * @return the <code>pivot</code>
     */
    public int getPivot() {
        return pivot;
    }

    /**
     * @param <code>pivot</code> the new value for <code>pivot</code>
     */
    public void setPivot(int pivot) {
        this.pivot = pivot;
    }

    /**
     * @return the <code>part</code>
     */
    public int getPart() {
        return part;
    }

    /**
     * @param <code>part</code> the new value for <code>part</code>
     */
    public void setPart(int part) {
        this.part = part;
    }

    /**
     * @return the <code>left</code> child. Contains the pivot in positive
     *         polarity.
     */
    public ResNode getLeft() {
        return left;
    }

    /**
     * @param <code>left</code> the new value for <code>left</code>
     */
    public void setLeft(ResNode left) {
        assert (left != null);
        this.left = left;
    }

    /**
     * @return the <code>right</code> child. Contains the pivot in negative
     *         polarity.
     */
    public ResNode getRight() {
        return right;
    }

    /**
     * @param <code>right</code> the new value for <code>right</code>
     */
    public void setRight(ResNode right) {
        assert (right != null);
        this.right = right;
    }

    /**
     * 
     * @return <code>true</code> iff this is a leaf.
     */
    public boolean isLeaf() {
        assert (!(left == null ^ right == null));
        return left == null && right == null;
    }

    public void print() {
        System.out.println("------------------------------------");
        if (isLeaf())
            System.out.println(id + "> (leaf) part:" + part);
        else
            System.out.println(id + "> left:" + left.id + " right:" + right.id
                    + " pivot:" + pivot);
        System.out.println("Clause: " + clause);
        Iterator<ResNode> itr = parents.iterator();
        System.out.print("Chidren: [");
        while (itr.hasNext()) {
            ResNode n = itr.next();
            System.out.print(n.id + ",");
        }
        System.out.println("]");
    }

    @Override
    public String toString() {
        if (left == null && right == null)
            return id + ":" + clause + " (p" + part + ")";
        else if (part != -1)
            return id + ":" + clause + " left:"
                    + (left == null ? "null" : left.id) + " right:"
                    + (right == null ? "null" : right.id) + " piv:" + pivot
                    + " (p" + part + ")";
        else
            return id + ":" + clause + " left:"
                    + (left == null ? "null" : left.id) + " right:"
                    + (right == null ? "null" : right.id) + " piv:" + pivot;
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(ResNode other) {
        return this.id - other.id;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.id;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof ResNode))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        ResNode other = (ResNode) obj;
        if (this.id != other.id)
            return false;
        if (this.part != other.part)
            return false;
        if (this.pivot != other.pivot)
            return false;
        if (!this.left.equals(other.left))
            return false;
        if (!this.right.equals(other.right))
            return false;
        if (!this.parents.equals(other.parents))
            return false;
        return true;
    }

    /**
     * @return the number of nodes in the subproof starting at this node,
     *         unwinding the DAG to a tree.
     */
    public int treeSize() {
        if (this.isLeaf())
            return 1;
        return this.left.treeSize() + this.right.treeSize() + 1;
    }

    /**
     * 
     * @param nodeSizes
     * @return DAG-aware computation of the tree size
     */
    public long treeSize(Map<ResNode, Long> nodeSizes) {
        if (nodeSizes.keySet().contains(this))
            return nodeSizes.get(this);

        if (this.isLeaf()) {
            nodeSizes.put(this, 1l);
            return 1;
        }

        long leftSize = this.left.treeSize(nodeSizes);
        long rightSize = this.right.treeSize(nodeSizes);

        long result = leftSize + rightSize + 1;
        nodeSizes.put(this, result);
        return result;
    }

    /**
     * 
     * @return a set of all descendants of this node.
     */
    public Set<ResNode> getDescendants() {
        Set<ResNode> result = new HashSet<ResNode>();
        this.getDescendantsRecursion(result);
        return result;
    }

    /**
     * Recursion for computing descendants
     * 
     * @param result
     *            descendants will be added to this set.
     */
    private void getDescendantsRecursion(Set<ResNode> result) {
        if (result.contains(this))
            return;
        result.add(this);
        if (!this.isLeaf()) {
            this.left.getDescendantsRecursion(result);
            this.right.getDescendantsRecursion(result);
        }
    }

}
