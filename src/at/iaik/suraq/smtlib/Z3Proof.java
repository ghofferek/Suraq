/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalEq;
import at.iaik.suraq.util.Util;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class Z3Proof implements SMTLibObject {

    protected Set<String> assertedStr = new HashSet<String>();

    /**
     * The proof type.
     */
    protected Token proofType;

    /**
     * The list of sub proofs.
     */
    protected List<Z3Proof> subProofs;

    /**
     * This formula is the consequent of this proof. It should either be an
     * <code>OrFormula</code> or the constant formula <code>false</code>.
     */
    protected Formula consequent;

    /**
     * A flag used for marking during recursive algorithms
     */
    private boolean marked = false;

    /**
     * Flag that indicates from which assert an asserted node comes. Only valid
     * for nodes of type ASSERTED.
     */
    private int assertPartition = 0;

    /**
     * A unique ID of the node.
     */
    private final int id;

    private static int instanceCounter = 0;

    /**
     * 
     * Constructs a new <code>Z3Proof</code>.
     * 
     */
    public Z3Proof() {
        this.proofType = null;
        this.subProofs = new ArrayList<Z3Proof>();
        this.consequent = null;
        this.id = Z3Proof.instanceCounter++;
    }

    /**
     * 
     * Constructs a new <code>Z3Proof</code>.
     * 
     * @param proofType
     *            the type of the proof
     * @param subProofs
     *            the list of all subproofs
     * @param consequent
     *            the formula which has to be proved
     */
    public Z3Proof(Token proofType, Z3Proof subProof1, Z3Proof subProof2,
            Formula consequent) {

        if (proofType == null)
            throw new RuntimeException("null prooftype not allowed!");

        this.proofType = proofType;
        this.subProofs = new ArrayList<Z3Proof>();
        if (subProof1 != null)
            this.subProofs.add(subProof1);
        if (subProof2 != null)
            this.subProofs.add(subProof2);
        this.consequent = consequent;
        this.id = Z3Proof.instanceCounter++;
    }

    /**
     * 
     * Constructs a new <code>Z3Proof</code>.
     * 
     * @param proofType
     *            the type of the proof
     * @param subProofs
     *            the list of all subproofs
     * @param consequent
     *            the formula which has to be proved
     */
    public Z3Proof(Token proofType, List<? extends Z3Proof> subProofs,
            Formula consequent) {

        if (proofType == null)
            throw new RuntimeException("null prooftype not allowed!");

        this.proofType = proofType;
        assert (subProofs != null);
        this.subProofs = new ArrayList<Z3Proof>();
        this.subProofs.addAll(subProofs);
        this.consequent = consequent;
        this.id = Z3Proof.instanceCounter++;

        if (proofType.equals(SExpressionConstants.ASSERTED)) {
            Set<Integer> partitions = consequent.getAssertPartition();
            assert (partitions.size() <= 2);
            partitions.remove(new Integer(-1));
            assert (partitions.size() == 1);
            if (partitions.size() > 0)
                assertPartition = partitions.iterator().next();
            else
                assertPartition = -1;
        }

    }

    /**
     * Creates a new <code>Z3Proof</code> which is of the same type as
     * <code>this</code> object and has the given subProofs and consequent.
     * 
     * @param subProofs
     *            List of sub-proofs
     * @param consequent
     *            the consequent
     * @return a new <code>Z3Proof</code> with the same type as
     *         <code>this</code>.
     */
    protected Z3Proof create(List<Z3Proof> subProofs, Formula consequent) {

        List<Z3Proof> newSubProofs = new ArrayList<Z3Proof>();

        for (Z3Proof subProof : subProofs) {
            newSubProofs.add(subProof);
        }

        Z3Proof instance = new Z3Proof(new Token(this.proofType), newSubProofs,
                consequent);

        return instance;
    }

    /**
     * Returns the type of the proof.
     * 
     * @return the <code>proofType</code>
     */
    public Token getProofType() {
        return this.proofType;
    }

    /**
     * Returns the list of sub proofs
     * 
     * @return the <code>thenBranch</code>
     */
    public List<Z3Proof> getSubProofs() {
        return this.subProofs;
    }

    /**
     * Returns the formula which has to be proved
     * 
     * @return the <code>consequent</code>
     */
    public Formula getConsequent() {
        return this.consequent;
    }

    /**
     * Converts this proof into an s-expression compatible with SMTLIBv2. Only
     * the proof itself is converted. No variable/function/macro declarations
     * are included.
     * 
     * @return this proof as an SMTLIBv2 s-expression.
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> children = new ArrayList<SExpression>();
        children.add(this.proofType);
        for (Z3Proof subProof : this.subProofs)
            children.add(subProof.toSmtlibV2());

        children.add(this.consequent.toSmtlibV2());
        return new SExpression(children);
    }

    /**
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.toSmtlibV2().toString();
    }

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getAssertPartition() {
        Set<Integer> partitions = consequent.getAssertPartition();

        for (Z3Proof proof : subProofs)
            partitions.addAll(proof.getAssertPartition());

        return partitions;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return System.identityHashCode(this);
    }

    /**
     * Compares the object references (pointers). This helps for distinguishing
     * trees from DAGs.
     * 
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        return (this == obj);
    }

    /**
     * This method is based on just looking at nodes with type ASSERTED and
     * checking from which assert statement they originate (according to their
     * own claim). Symbols are not checked.
     * 
     * This method and the returned set does not have a notion of "global". If
     * the subtree is just from one assert statement, the cardinality of the
     * returned set should be 1.
     * 
     * @return
     */
    public Set<Integer> getAssertedPartitions() {

        Set<Integer> assertPartitions = new HashSet<Integer>();
        for (Z3Proof z3Proofchild : this.subProofs) {
            assertPartitions.addAll(z3Proofchild.getAssertedPartitions());
        }

        if (proofType.equals(SExpressionConstants.ASSERTED)) {
            assertPartitions.add(new Integer(assertPartition));
        }

        return assertPartitions;
    }

    public Set<Z3Proof> getLemmas() {

        Set<Z3Proof> lemmas = new HashSet<Z3Proof>();
        if (proofType.equals(SExpressionConstants.LEMMA)) {
            lemmas.add(this);
        }
        for (Z3Proof z3Proofchild : this.subProofs) {
            lemmas.addAll(z3Proofchild.getLemmas());
        }
        return lemmas;
    }

    public void localLemmasToAssertions() {
        if (proofType.equals(SExpressionConstants.LEMMA)) {
            assert (subProofs.size() == 1);
            Set<Integer> assertedPartitions = subProofs.get(0)
                    .getAssertedPartitions();
            if (assertedPartitions.size() > 1)
                return;
            Set<Integer> symbolsPartitions = consequent.getAssertPartition();
            symbolsPartitions.remove(new Integer(-1));
            if (assertedPartitions.equals(symbolsPartitions)) {
                proofType = SExpressionConstants.ASSERTED;
                assert (assertedPartitions.size() == 1);
                assertPartition = assertedPartitions.iterator().next();
                subProofs = new ArrayList<Z3Proof>();
                return;
            } else
                return;
        }

        else
            for (Z3Proof child : subProofs)
                child.localLemmasToAssertions();

    }

    public void removeLocalSubProofs() {
        // FIXME Very inefficient! Cache results of getAssertFormulas!!
        if (this.getAssertedPartitions().size() == 1) {
            Set<Integer> thisPartitions = this.getAssertedPartitions();
            boolean isLocal = true;
            // Set<Z3Proof> lemmas = this.getLemmas();
            // for (Z3Proof lemma : lemmas) {
            // Set<Integer> lemmaPartitions = lemma.getAssertPartition();
            // thisPartitions.remove(new Integer(-1));
            // lemmaPartitions.remove(new Integer(-1));
            // if (!thisPartitions.equals(lemmaPartitions)) {
            // isLocal = false;
            // break;
            // }
            // }

            if (isLocal) {
                proofType = SExpressionConstants.ASSERTED;
                subProofs = new ArrayList<Z3Proof>();
                return;
            }
        }
        for (Z3Proof child : subProofs) {
            child.removeLocalSubProofs();
        }
    }

    public void dealWithModusPonens() {

        if (proofType.equals(SExpressionConstants.MODUS_PONENS)) {
            assert (subProofs.size() == 2);
            Z3Proof child1 = subProofs.get(0);
            if (Util.checkForFlippedDisequality(this.consequent,
                    child1.consequent)) {
                // TransformedZ3Proof premise = new
                // TransformedZ3Proof(SExpressionConstants.ASSERTED, new
                // ArrayList<TransformedZ3Proof>(), child1.consequent);
                // TransformedZ3Proof symmProof =
                // TransformedZ3Proof.createSymmetrieProof(premise);
                this.subProofs.clear();
                this.subProofs.add(child1);
                this.proofType = SExpressionConstants.SYMMETRY;
                child1.dealWithModusPonens();
                return;
            }
            assert (child1.hasSingleLiteralConsequent());
            Formula literal1 = Util.getSingleLiteral(child1.consequent);

            Z3Proof child2 = subProofs.get(1);
            Z3Proof child3 = null;
            assert (child2.consequent instanceof PropositionalEq);
            while (true) {
                if (child2.subProofs.size() == 1)
                    child2 = child2.subProofs.get(0);
                else {
                    assert (child2.subProofs.size() == 2);
                    child2 = subProofs.get(0);
                    child3 = subProofs.get(1);
                    assert (child2.hasSingleLiteralConsequent());
                    assert (child3.hasSingleLiteralConsequent());
                    break;
                }
            }
            Formula literal2 = Util.getSingleLiteral(child2.consequent);
            Formula literal3 = Util.getSingleLiteral(child3.consequent);

            // FIXME NOT FINISHED YET!!

            // Don't forget the recursive calls on the children!
            child1.dealWithModusPonens();
            child2.dealWithModusPonens();
            child3.dealWithModusPonens();
            return;
        }

        for (Z3Proof child : subProofs) {
            child.dealWithModusPonens();
        }
    }

    public String prettyPrint() {
        if (this.marked)
            return "";
        marked = true;
        StringBuffer result = new StringBuffer();
        result.append("----------------------------------------------\n");
        result.append("ID: ");
        result.append(this.id);
        result.append("\n");
        result.append("Rule: ");
        result.append(proofType.toString());
        result.append("\n");
        result.append("Antecedents:\n");
        for (Z3Proof child : subProofs) {
            result.append(child.id);
            result.append(": ");
            result.append(child.consequent.toString()
                    .replaceAll("\\s{2,}", " "));
            result.append("\n");
        }
        result.append("Proofs: ");
        result.append(consequent.toString().replaceAll("\\s{2,}", " ")
                .replace("\n", ""));
        result.append("\n");
        for (Z3Proof child : subProofs)
            result.append(child.prettyPrint());
        return result.toString();
    }

    public void resetMarks() {
        marked = false;
        for (Z3Proof child : subProofs)
            child.resetMarks();
    }

    /**
     * @return <code>true</code> if the consequent of this node has only a
     *         single literal.
     */
    protected boolean hasSingleLiteralConsequent() {
        if (!(this.consequent instanceof OrFormula))
            return false;
        OrFormula consequent = (OrFormula) this.consequent;
        return consequent.getDisjuncts().size() == 1;
    }

}
