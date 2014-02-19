/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.io.Serializable;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.EqualityFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.FormulaTerm;
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalEq;
import at.iaik.suraq.smtlib.formula.PropositionalTerm;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.smtsolver.SMTSolver;
import at.iaik.suraq.util.DagOperationManager;
import at.iaik.suraq.util.ImmutableSet;
import at.iaik.suraq.util.SoftReferenceWithEquality;
import at.iaik.suraq.util.Timer;
import at.iaik.suraq.util.Util;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 */
public class Z3Proof implements SMTLibObject, Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = 7871807524124015582L;

    protected static final DecimalFormat myFormatter = new DecimalFormat(
            "###,###,###");

    /**
     * lists operations which already traversed this node.
     */
    protected Set<Long> visitedByOperation = new HashSet<Long>();

    @Deprecated
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
     * The set of parents of this node.
     */
    protected Set<SoftReferenceWithEquality<Z3Proof>> parents = null;

    /**
     * This formula is the consequent of this proof. It should either be an
     * <code>OrFormula</code> or the constant formula <code>false</code>.
     */
    protected Formula consequent;

    /**
     * Flag that indicates from which assert an asserted node comes. Only valid
     * for nodes of type ASSERTED.
     */
    protected int assertPartition = 0;

    /**
     * A unique ID of the node.
     */
    protected final int id;

    /**
     * Specifies if this proof object is an axiom introduced during
     * transformation.
     */
    protected boolean axiom = false;

    private static int instanceCounter = 1;

    /**
     * A cache for hypotheses on which this node depends.
     */
    protected ImmutableSet<Z3Proof> hypothesesCache = null;

    /**
     * A cache for hypothesis formulas.
     */
    protected ImmutableSet<Formula> hypothesisFormulasCache = null;

    /**
     * Store the modification counter at which the hypotheses cache was last
     * updated
     * 
     * @deprecated use hypCacheDirty flag instead
     */
    @Deprecated
    protected long hypCacheModCount = 0;

    /**
     * Indicated whether the hypotheses cache is dirty or usable.
     */
    protected boolean hypCacheDirty = true;

    /**
     * The set of literals that have become obsolete by proof rewriting.
     * Resolutions with these literals are no longer necessary. Literals are
     * added in the reverse polarity of that in which they would originally have
     * occurred in this node. I.e., the polarity is the same as that of the
     * corresponding hypothesis (that is no longer present), and also the same
     * of the one that is supposed to occur in another node with which this one
     * will be resolved. I.e., the clause that contains the literal in the same
     * polarity as in this set is the obsolete clause. The set should contain
     * the literals directly, not their unit clauses.
     */
    protected ImmutableSet<Formula> obsoleteLiterals = null;

    /**
     * Is incremented every time a structural change is made to the proof DAG,
     * which might affect the hypotheses cache.
     * 
     */
    protected static long hypModCount = 0;

    private static final Timer debugGetHypothesesTimer = new Timer();

    private static long debugGetHypothesesCallCounter = 0;

    private static long debugGetHypothesesCallUsingCacheCounter = 0;

    private static long debugLastGetHypothesesStatsTime = 0;

    private static final void printDebugGetHypothesesTimerStats() {
        if ((Z3Proof.debugGetHypothesesTimer.getTotalTimeMillis() - Z3Proof.debugLastGetHypothesesStatsTime) > 60000) {
            Z3Proof.debugLastGetHypothesesStatsTime = Z3Proof.debugGetHypothesesTimer
                    .getTotalTimeMillis();
            System.out
                    .println("INFO: Spent a total of "
                            + Z3Proof.debugGetHypothesesTimer
                            + " on "
                            + Z3Proof.myFormatter
                                    .format(Z3Proof.debugGetHypothesesCallCounter)
                            + " calls ("
                            + Z3Proof.myFormatter
                                    .format(Z3Proof.debugGetHypothesesCallUsingCacheCounter)
                            + " calls using cache) to get hypotheses(formulas).");
        }
    }

    /**
     * 
     * Constructs a new <code>Z3Proof</code>.
     * 
     */
    public Z3Proof() {
        this.proofType = null;
        this.subProofs = new ArrayList<Z3Proof>();
        this.parents = new HashSet<SoftReferenceWithEquality<Z3Proof>>();
        this.consequent = null;
        this.id = Z3Proof.instanceCounter++;
        if (this.id == 1063)
            assert (this.id != 1468192489);
        if (this.id % 1000 == 0) {
            String output = Z3Proof.myFormatter.format(this.id);
            System.out.println("INFO: Created the " + output + " proof node.");
        }
        // this.assertPartition = -1;
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
        this.parents = new HashSet<SoftReferenceWithEquality<Z3Proof>>();
        if (subProof1 != null)
            this.subProofs.add(subProof1);
        if (subProof2 != null)
            this.subProofs.add(subProof2);
        this.consequent = consequent;
        this.id = Z3Proof.instanceCounter++;
        if (this.id == 1063)
            assert (this.id != 1468192489);
        if (this.id % 1000 == 0) {
            String output = Z3Proof.myFormatter.format(this.id);
            System.out.println("INFO: Created the " + output + " proof node.");
        }
        this.setAssertPartition();
        // assert (this.checkZ3ProofNode());
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
        this(proofType, subProofs, consequent, 0, false);
        this.setAssertPartition();
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
     * @param partition
     *            the partition for this node. (Only used if
     *            <code>proofType</code> equals <code>ASSERTED</code>.)
     * @param axiom
     *            <code>true</code> if this is an axiom.
     */
    public Z3Proof(Token proofType, List<? extends Z3Proof> subProofs,
            Formula consequent, int partition, boolean axiom) {
        this.axiom = axiom;
        if (proofType == null)
            throw new RuntimeException("null prooftype not allowed!");

        this.proofType = proofType;
        assert (subProofs != null);
        this.subProofs = new ArrayList<Z3Proof>();
        this.parents = new HashSet<SoftReferenceWithEquality<Z3Proof>>();
        this.subProofs.addAll(subProofs);
        this.consequent = consequent;
        this.id = Z3Proof.instanceCounter++;
        if (this.id == 1063)
            assert (this.id != 1468192489);
        if (this.id % 1000 == 0) {
            String output = Z3Proof.myFormatter.format(this.id);
            System.out.println("INFO: Created the " + output + " proof node.");
        }
        if (this.proofType.equals(SExpressionConstants.ASSERTED)) {
            if (partition > 0)
                assertPartition = partition;
            else {
                Set<Integer> symbolPartitions = consequent
                        .getPartitionsFromSymbols();
                symbolPartitions.remove(-1);
                if (symbolPartitions.isEmpty())
                    assertPartition = 1; // arbitrary choice
                else {
                    if (symbolPartitions.size() != 1)
                        assert (false);
                    assertPartition = symbolPartitions.iterator().next();
                }
            }
            assert (assertPartition > 0);
        }
        // assert (this.checkZ3ProofNode());
    }

    private void setAssertPartition() {
        if (proofType.equals(SExpressionConstants.ASSERTED)) {
            Set<Integer> partitions = consequent.getPartitionsFromSymbols();
            assert (partitions.size() <= 2);
            partitions.remove(new Integer(-1));

            if (partitions.size() > 0) {
                assert (partitions.size() == 1);
                assertPartition = partitions.iterator().next();
            } else
                assertPartition = 1; // arbitrary choice for globals
            assert (assertPartition > 0);
        }
    }

    /**
     * @param proof
     */
    protected void takeValuesFrom(Z3Proof proof) {
        this.axiom = proof.axiom;
        this.subProofs = new ArrayList<Z3Proof>(proof.subProofs);

        // parents are not copied.
        // This node only takes the "values" of the other node.
        // its position in the DAG stays the same.

        
        Z3Proof.hypModCount++;
        this.hypCacheModCount = proof.hypCacheModCount;
        this.hypCacheDirty = proof.hypCacheDirty;
        if (this.hypCacheDirty)
            this.markHypCacheDirty();
        this.hypothesesCache = proof.hypothesesCache;
        this.hypothesisFormulasCache = proof.hypothesisFormulasCache;
        this.proofType = proof.proofType;
        this.consequent = proof.consequent;
        this.assertPartition = proof.assertPartition;
        assert (this.assertPartition > 0 || !this.proofType
                .equals(SExpressionConstants.ASSERTED));
    }

    public void addParent(Z3Proof parent) {
        SoftReferenceWithEquality<Z3Proof> ref = new SoftReferenceWithEquality<Z3Proof>(
                parent);
        if (parents == null)
            parents = new HashSet<SoftReferenceWithEquality<Z3Proof>>();
        if (!parents.contains(ref))
            parents.add(ref);
    }

    public void addParents(Collection<? extends Z3Proof> parents) {
        for (Z3Proof parent : parents)
            this.addParent(parent);
    }

    public void removeParent(Z3Proof parent) {
        assert (parents != null);
        parents.remove(new SoftReferenceWithEquality<Z3Proof>(parent));
    }

    public Set<Z3Proof> getParents() {
        if (parents == null)
            return new HashSet<Z3Proof>(0);
        Set<Z3Proof> result = new HashSet<Z3Proof>();
        for (SoftReferenceWithEquality<Z3Proof> ref : parents)
            result.add(ref.get());
        return result;
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
    @Deprecated
    protected Z3Proof create(List<Z3Proof> subProofs, Formula consequent) {

        List<Z3Proof> newSubProofs = new ArrayList<Z3Proof>();

        for (Z3Proof subProof : subProofs) {
            newSubProofs.add(subProof);
        }

        Z3Proof instance = new Z3Proof(Token.generate(this.proofType), newSubProofs,
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
     * @return the <code>subProofs</code> (live list!)
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

    public void addObsoleteLiteral(Formula literal) {
        assert (Util.isLiteral(literal));
        obsoleteLiterals = obsoleteLiterals.addToCopy(literal);
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
    public Set<Integer> getPartitionsFromSymbols() {
        long operationId = DagOperationManager.startDAGOperation();
        Set<Integer> result = this
                .getPartitionsFromSymbolsRecursion(operationId);
        DagOperationManager.endDAGOperation(operationId);
        return result;
    }

    private Set<Integer> getPartitionsFromSymbolsRecursion(long operationId) {
        visitedByDAGOperation(operationId);

        Set<Integer> partitions = consequent.getPartitionsFromSymbols();

        for (Z3Proof proof : subProofs) {
            if (proof.wasVisitedByDAGOperation(operationId))
                continue;
            partitions.addAll(proof
                    .getPartitionsFromSymbolsRecursion(operationId));
        }
        return partitions;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.id;
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

    public Set<Integer> getPartitionsFromAsserts() {
        long operationId = DagOperationManager.startDAGOperation();
        Set<Integer> result = new HashSet<Integer>();
        this.getPartitionsFromAssertsRecursion(operationId, result);
        DagOperationManager.endDAGOperation(operationId);
        return result;
    }

    private void getPartitionsFromAssertsRecursion(long operationId,
            Set<Integer> result) {

        visitedByDAGOperation(operationId);
        assert (result != null);

        for (Z3Proof z3Proofchild : this.subProofs) {
            if (z3Proofchild.wasVisitedByDAGOperation(operationId))
                continue;
            z3Proofchild.getPartitionsFromAssertsRecursion(operationId, result);
        }

        if (proofType.equals(SExpressionConstants.ASSERTED)) {
            if (assertPartition <= 0)
                assert (false);
            result.add(new Integer(assertPartition));
        }
    }

    public int getID() {
        return this.id;
    }

    public String getIdString() {
        return Z3Proof.myFormatter.format(id);
    }

    /**
     * Gets all the lemmas that "close" any hypothesis that <code>this</code>
     * node depends on.
     * 
     * @return lemmas found <code>this</code> node "upwards" (towards parents).
     */
    public Set<Z3Proof> getClosingLemmas() {
        long operationId = DagOperationManager.startDAGOperation();
        Set<Z3Proof> result = new HashSet<Z3Proof>();
        this.getClosingLemmasRecursion(operationId, result);
        DagOperationManager.endDAGOperation(operationId);
        return result;
    }

    private void getClosingLemmasRecursion(long operationId, Set<Z3Proof> result) {
        if (wasVisitedByDAGOperation(operationId))
            return;
        visitedByDAGOperation(operationId);
        if (this.proofType.equals(SExpressionConstants.LEMMA)) {
            result.add(this);
            return;
        }
        if (parents != null) {
            for (SoftReferenceWithEquality<Z3Proof> parentRef : parents) {
                Z3Proof parent = parentRef.get();
                if (parent != null)
                    parent.getClosingLemmasRecursion(operationId, result);
            }
        }
    }

    /**
     * Gets all the lemmas that occur in subproofs.
     * 
     * @return lemmas found from <code>this</code> node "downwards" (towards
     *         parents).
     */
    public Set<Z3Proof> getLemmas() {
        long operationId = DagOperationManager.startDAGOperation();
        Set<Z3Proof> result = this.getLemmasRecursion(operationId);
        DagOperationManager.endDAGOperation(operationId);
        return result;
    }

    private Set<Z3Proof> getLemmasRecursion(long operationId) {
        visitedByDAGOperation(operationId);

        Set<Z3Proof> lemmas = new HashSet<Z3Proof>();
        if (proofType.equals(SExpressionConstants.LEMMA)) {
            lemmas.add(this);
        }
        for (Z3Proof z3Proofchild : this.subProofs) {
            if (z3Proofchild.wasVisitedByDAGOperation(operationId))
                continue;
            lemmas.addAll(z3Proofchild.getLemmasRecursion(operationId));
        }
        return lemmas;
    }

    public ImmutableSet<Formula> getHypothesisFormulas() {
        Z3Proof.debugGetHypothesesCallCounter++;
        Z3Proof.debugGetHypothesesTimer.start();

        if (hypothesisFormulasCache != null) {
            // if (this.hypCacheModCount == Z3Proof.hypModCount) {
            if (!this.hypCacheDirty) {
                Z3Proof.debugGetHypothesesCallUsingCacheCounter++;
                Z3Proof.debugGetHypothesesTimer.stop();
                Z3Proof.printDebugGetHypothesesTimerStats();
                return hypothesisFormulasCache;
            }
        }

        Set<Z3Proof> hypotheses = this.getHypotheses();
        Z3Proof.debugGetHypothesesTimer.start(); // timer is stopped by the call
                                                 // above.
        Set<Formula> tmp = new HashSet<Formula>();
        for (Z3Proof hypothesis : hypotheses)
            tmp.add(hypothesis.getConsequent().transformToConsequentsForm());
        hypothesisFormulasCache = ImmutableSet.create(tmp);
        Z3Proof.debugGetHypothesesTimer.stop();
        Z3Proof.printDebugGetHypothesesTimerStats();
        return hypothesisFormulasCache;
    }

    public Set<Z3Proof> getHypotheses() {
        Z3Proof.debugGetHypothesesCallCounter++;
        Z3Proof.debugGetHypothesesTimer.start();

        if (hypothesesCache != null) {
            // if (this.hypCacheModCount == Z3Proof.hypModCount) {
            if (!this.hypCacheDirty) {
                Z3Proof.debugGetHypothesesCallUsingCacheCounter++;
                Z3Proof.debugGetHypothesesTimer.stop();
                Z3Proof.printDebugGetHypothesesTimerStats();
                return hypothesesCache;
            }
        }
        
        long operationId = DagOperationManager.startDAGOperation();
        Set<Z3Proof> result = this.getHypothesesRecursion(operationId);
        DagOperationManager.endDAGOperation(operationId);
        if (!result.equals(hypothesesCache) || hypothesesCache == null
                || hypothesisFormulasCache == null) {
            hypothesesCache = ImmutableSet.create(result);
            Set<Formula> tmp = new HashSet<Formula>();
            for (Z3Proof hypothesis : result)
                tmp.add(hypothesis.getConsequent().transformToConsequentsForm());
            hypothesisFormulasCache = ImmutableSet.create(tmp);
            this.markHypCacheDirty();
        }
        this.hypCacheModCount = Z3Proof.hypModCount;
        
        this.hypCacheDirty = false;
        Z3Proof.debugGetHypothesesTimer.stop();
        Z3Proof.printDebugGetHypothesesTimerStats();
        return hypothesesCache;
    }

    private Set<Z3Proof> getHypothesesRecursion(long operationId) {
        visitedByDAGOperation(operationId);

        if (!this.hypCacheDirty) {
            assert (hypothesesCache != null);
            return hypothesesCache;
        }

        if (proofType.equals(SExpressionConstants.LEMMA)) {
            this.hypCacheDirty = false;
            this.hypothesesCache = ImmutableSet.create(new HashSet<Z3Proof>());
            return hypothesesCache;
        }

        if (proofType.equals(SExpressionConstants.HYPOTHESIS)) {
            assert (this.subProofs.size() == 0);
            this.hypothesesCache = ImmutableSet.create(Collections
                    .singleton(this));
            this.hypCacheDirty = false;
            return hypothesesCache;
        }
        if (this instanceof TransformedZ3Proof) {
            if (((TransformedZ3Proof) this).isHypothesis()) {
                assert (this.subProofs.size() == 0);
                this.hypothesesCache = ImmutableSet.create(Collections
                        .singleton(this));
                this.hypCacheDirty = false;
                return hypothesesCache;
            }
        }

        Set<Z3Proof> tmp = new HashSet<Z3Proof>();
        for (Z3Proof z3Proofchild : this.subProofs) {
            if (z3Proofchild.wasVisitedByDAGOperation(operationId)) {
                assert (!z3Proofchild.hypCacheDirty);
                tmp.addAll(z3Proofchild.hypothesesCache);
            } else {
                tmp.addAll(z3Proofchild.getHypothesesRecursion(operationId));
            }
        }
        this.hypothesesCache = ImmutableSet.create(tmp);
        this.hypCacheDirty = false;
        return hypothesesCache;
    }

    /**
     * Marks the hypothesis cache of this node and all its ancestors as dirty.
     */
    public void markHypCacheDirty() {
        this.hypCacheDirty = true;
        for (Z3Proof ancestor : this.allAncestorNodes())
            ancestor.hypCacheDirty = true;
    }

    @Deprecated
    public void localLemmasToAssertions() {
        long operationId = DagOperationManager.startDAGOperation();
        this.localLemmasToAssertionsRecursion(operationId);
        DagOperationManager.endDAGOperation(operationId);
    }

    @Deprecated
    private void localLemmasToAssertionsRecursion(long operationId) {
        visitedByDAGOperation(operationId);

        if (proofType.equals(SExpressionConstants.LEMMA)) {
            assert (subProofs.size() == 1);

            Set<Integer> partitionsFromAsserts = subProofs.get(0)
                    .getPartitionsFromAsserts();
            assert (!partitionsFromAsserts.contains(new Integer(-1)));

            if (partitionsFromAsserts.size() > 1) {
                if (!(subProofs.get(0).wasVisitedByDAGOperation(operationId)))
                    subProofs.get(0).localLemmasToAssertionsRecursion(
                            operationId);
                return;
            }

            Set<Integer> symbolsPartitions = consequent
                    .getPartitionsFromSymbols();
            symbolsPartitions.remove(new Integer(-1));
            if (partitionsFromAsserts.equals(symbolsPartitions)) {
                proofType = SExpressionConstants.ASSERTED;
                if (partitionsFromAsserts.size() == 1)
                    assertPartition = partitionsFromAsserts.iterator().next();
                else if (partitionsFromAsserts.size() == 0)
                    assertPartition = 1; // arbitrary choice
                else
                    assert (false); // unreachable
                assert (assertPartition > 0);
                subProofs = new ArrayList<Z3Proof>();
                return;
            } else
                return;
        } else
            for (Z3Proof child : subProofs) {
                if (child.wasVisitedByDAGOperation(operationId))
                    continue;
                child.localLemmasToAssertionsRecursion(operationId);
            }

    }

    /**
     * Removes local subproofs (including lemmas, if they are local).
     */
    public void removeLocalSubProofs() {
        long operationId = DagOperationManager.startDAGOperation();
        Map<Z3Proof, Set<Integer>> partitionMap = new HashMap<Z3Proof, Set<Integer>>();
        Map<Z3Proof, Boolean> existHypothesesMap = new HashMap<Z3Proof, Boolean>();
        this.removeLocalSubProofsRecursion(operationId, partitionMap,
                existHypothesesMap);
        DagOperationManager.endDAGOperation(operationId);
    }

    private void removeLocalSubProofsRecursion(long operationId,
            Map<Z3Proof, Set<Integer>> partitionMap,
            Map<Z3Proof, Boolean> existHypothesesMap) {
        assert (!this.wasVisitedByDAGOperation(operationId));
        this.visitedByDAGOperation(operationId);
        assert (partitionMap != null);
        assert (existHypothesesMap != null);

        Set<Integer> partitions = new HashSet<Integer>();
        boolean existHypotheses = false;

        if (this.proofType.equals(SExpressionConstants.HYPOTHESIS)) {
            existHypotheses = true;
            partitions.addAll(this.consequent.getPartitionsFromSymbols());
        } else if (this.proofType.equals(SExpressionConstants.ASSERTED)) {
            assert (this.assertPartition > 0);
            partitions.add(this.assertPartition);

        }

        for (Z3Proof child : this.subProofs) {
            if (!child.wasVisitedByDAGOperation(operationId))
                child.removeLocalSubProofsRecursion(operationId, partitionMap,
                        existHypothesesMap);

            assert (partitionMap.containsKey(child));
            Set<Integer> childPartitions = partitionMap.get(child);
            assert (childPartitions != null);
            partitions.addAll(childPartitions);

            assert (existHypothesesMap.containsKey(child));
            Boolean existChildHypotheses = existHypothesesMap.get(child);
            assert (existChildHypotheses != null);
            existHypotheses |= existChildHypotheses;
        }

        partitionMap.put(this, new HashSet<Integer>(partitions));
        existHypothesesMap.put(this, existHypotheses);
        partitions.remove(-1);

        if (this.proofType.equals(SExpressionConstants.LEMMA)
                || !existHypotheses) {
            if (partitions.size() <= 1) {
                int partition = partitions.size() == 0 ? 1 : partitions
                        .iterator().next(); // arbitrary choice 1 for
                                            // "global facts"
                this.subProofs = new ArrayList<Z3Proof>(0);
                this.proofType = SExpressionConstants.ASSERTED;
                this.assertPartition = partition;
                assert (this.assertPartition > 0);
            }
        }

        // DEBUG
        // int mapSize = partitionMap.keySet().size();
        // if (mapSize % 100 == 0) {
        // DecimalFormat myFormatter = new DecimalFormat("###,###,###");
        // String output = myFormatter.format(mapSize);
        // System.out.println("  DEBUG-INFO: Already " + output
        // + " nodes in partitionMap.");
        // }
        // END DEBUG

    }

    public String prettyPrint() {
        long operationId = DagOperationManager.startDAGOperation();
        StringBuffer buffer = new StringBuffer();
        this.prettyPrintRecursive(operationId, buffer);
        DagOperationManager.endDAGOperation(operationId);
        return buffer.toString();
    }

    private void prettyPrintRecursive(long operationId, StringBuffer buffer) {
        visitedByDAGOperation(operationId);

        buffer.append("----------------------------------------------\n");
        buffer.append("ID: ");
        buffer.append(this.id);
        buffer.append("  (partition: ");
        buffer.append(this.assertPartition);
        buffer.append(")");
        buffer.append("\n");
        buffer.append("Rule: ");
        buffer.append(proofType.toString());
        buffer.append("\n");
        buffer.append("Antecedents:\n");
        for (Z3Proof child : subProofs) {
            buffer.append(child.id);
            buffer.append(": ");
            buffer.append(child.consequent.toString()
                    .replaceAll("\\s{2,}", " ").replace("\n", ""));
            buffer.append("\n");
        }
        buffer.append("Proofs: ");
        buffer.append(consequent.toString().replaceAll("\\s{2,}", " ")
                .replace("\n", ""));
        buffer.append("\n");
        for (Z3Proof child : subProofs) {
            if (child.wasVisitedByDAGOperation(operationId))
                continue;
            child.prettyPrintRecursive(operationId, buffer);
        }
    }

    /**
     * marks a node as visited by this operation.
     * 
     * @param operationId
     *            unique id of the operation.
     */
    protected void visitedByDAGOperation(long operationId) {
        // check for consistency.
        if (this.visitedByOperation.contains(operationId))
            throw new RuntimeException("revisited node#" + this.id
                    + " with operation#" + operationId
                    + ". this should not happen!");

        this.visitedByOperation.removeAll(DagOperationManager
                .getFinishedOperations());
        this.visitedByOperation.add(operationId);
        DagOperationManager.incrementNodeCounter(operationId);
    }

    /**
     * checks if this node was already visited by this operation.
     * 
     * @param operationId
     *            unique id of the operation.
     * @return true if was visited.
     */
    protected boolean wasVisitedByDAGOperation(long operationId) {
        return this.visitedByOperation.contains(operationId);
    }

    /**
     * 
     * @return the set of all nodes in this DAG.
     */
    public Set<Z3Proof> allNodes() {
        Set<Z3Proof> result = new HashSet<Z3Proof>();
        this.allNodes(result);
        return result;
    }

    private void allNodes(Set<Z3Proof> set) {
        set.add(this);
        for (Z3Proof child : this.subProofs) {
            if (!set.contains(child))
                child.allNodes(set);
        }
    }

    /**
     * 
     * @return the set of all ancestor nodes of <code>this</code>.
     */
    public Set<Z3Proof> allAncestorNodes() {
        Set<Z3Proof> result = new HashSet<Z3Proof>();
        this.allAncestorNodes(result);
        result.remove(this);
        return result;
    }

    private void allAncestorNodes(Set<Z3Proof> set) {
        set.add(this);
        if (parents != null) {
            for (SoftReferenceWithEquality<Z3Proof> parentRef : this.parents) {
                Z3Proof parent = parentRef.get();
                assert (parent != null);
                if (!set.contains(parent))
                    parent.allAncestorNodes(set);
            }
        }
    }

    /**
     * @return <code>true</code> if the consequent of this node has only a
     *         single literal.
     */
    protected boolean hasSingleLiteralConsequent() {

        Formula formula = this.consequent.transformToConsequentsForm();
        if (!(formula instanceof OrFormula))
            return false;
        OrFormula consequent = (OrFormula) formula;
        return consequent.getDisjuncts().size() == 1;
    }

    /**
     * Creates a transitivity proof for the given list of subproofs. The list
     * must have exactly two or three elements, which match a transitivity
     * premise of the form [(a=b), (b=c)] or [(a=b), (b=c), (c=d)].
     * 
     * @param subProofs
     *            the subproofs
     * @return a transitivity proof for the given term.
     */
    public static Z3Proof createTransitivityProof(
            List<? extends Z3Proof> subProofs) {
        assert (subProofs != null);
        assert (!subProofs.isEmpty());
        subProofs = new ArrayList<Z3Proof>(subProofs);
        List<TransformedZ3Proof> transformedSubProofs = new ArrayList<TransformedZ3Proof>(
                subProofs.size());
        if (subProofs.size() == 1) {
            return subProofs.get(0);
        }
        assert (Util.makeLiteralPositive(Util.getSingleLiteral((subProofs
                .get(0).consequent.transformToConsequentsForm()))) instanceof EqualityFormula);
        assert (Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs.get(1).consequent
                        .transformToConsequentsForm())) instanceof EqualityFormula);
        assert (subProofs.size() == 3 ? Util.makeLiteralPositive(Util
                .getSingleLiteral(subProofs.get(2).consequent
                        .transformToConsequentsForm())) instanceof EqualityFormula
                : true);

        final int initialSize = subProofs.size();

        Set<Z3Proof> toRemove = new HashSet<Z3Proof>();
        for (Z3Proof subProof : subProofs) {
            if (Util.isReflexivity(subProof.consequent))
                toRemove.add(subProof);
        }
        subProofs.removeAll(toRemove);
        if (subProofs.size() < 2) {
            if (subProofs.size() == 1)
                return subProofs.get(0);
            else {
                assert (subProofs.size() == 0);
                assert (toRemove.size() == initialSize);
                Object[] proofs = toRemove.toArray();
                assert (proofs.length == initialSize);
                assert (proofs.length == 2 || proofs.length == 3);
                assert (proofs[0] instanceof Z3Proof);
                assert (proofs[1] instanceof Z3Proof);
                if (proofs.length > 2) {
                    assert (proofs[2] instanceof Z3Proof);
                    assert (((Z3Proof) proofs[0]).consequent
                            .equals(((Z3Proof) proofs[1]).consequent) && ((Z3Proof) proofs[1]).consequent
                            .equals(((Z3Proof) proofs[2]).consequent));
                } else {
                    assert (((Z3Proof) proofs[0]).consequent
                            .equals(((Z3Proof) proofs[1]).consequent));
                }
                Z3Proof result = (proofs[0] instanceof TransformedZ3Proof) ? new TransformedZ3Proof(
                        SExpressionConstants.ASSERTED,
                        new ArrayList<TransformedZ3Proof>(),
                        ((Z3Proof) proofs[0]).consequent) : new Z3Proof(
                        SExpressionConstants.ASSERTED,
                        new ArrayList<Z3Proof>(),
                        ((Z3Proof) proofs[0]).consequent);
                result.axiom = true;
                return result;
            }
        }

        if (subProofs.size() > 3) {
            if (subProofs.get(0) instanceof TransformedZ3Proof) {
                for (Z3Proof subProof : subProofs) {
                    assert (subProof instanceof TransformedZ3Proof);
                    transformedSubProofs.add((TransformedZ3Proof) subProof);
                }
                Z3Proof intermediate = (subProofs.get(0) instanceof TransformedZ3Proof) ? TransformedZ3Proof
                        .createTransitivityProofForTransformedZ3Proofs(new ArrayList<TransformedZ3Proof>(
                                transformedSubProofs.subList(0, 2)))
                        : Z3Proof
                                .createTransitivityProof(new ArrayList<Z3Proof>(
                                        subProofs.subList(0, 2)));
                for (int count = 2; count < subProofs.size(); count++) {
                    List<Z3Proof> currentSubProofs = new ArrayList<Z3Proof>(2);
                    // / FIXME ugly hack to deal with transformed proofs.
                    List<TransformedZ3Proof> transformedCurrentSubProofs = new ArrayList<TransformedZ3Proof>(
                            2);
                    currentSubProofs.add(intermediate);
                    currentSubProofs.add(subProofs.get(count));
                    if (intermediate instanceof TransformedZ3Proof
                            && subProofs.get(count) instanceof TransformedZ3Proof) {
                        transformedCurrentSubProofs
                                .add((TransformedZ3Proof) intermediate);
                        transformedCurrentSubProofs
                                .add((TransformedZ3Proof) subProofs.get(count));
                    }
                    intermediate = (subProofs.get(0) instanceof TransformedZ3Proof) ? TransformedZ3Proof
                            .createTransitivityProofForTransformedZ3Proofs(new ArrayList<TransformedZ3Proof>(
                                    transformedCurrentSubProofs.subList(0, 2)))
                            : Z3Proof.createTransitivityProof(currentSubProofs);
                }
                return intermediate;
            }
        }

        EqualityFormula firstFormula = (EqualityFormula) Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs.get(0).consequent
                        .transformToConsequentsForm()));
        EqualityFormula lastFormula = (EqualityFormula) Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs
                        .get(subProofs.size() - 1).consequent
                        .transformToConsequentsForm()));
        EqualityFormula middleFormula = subProofs.size() == 3 ? (EqualityFormula) Util
                .makeLiteralPositive(Util.getSingleLiteral(subProofs.get(1).consequent
                        .transformToConsequentsForm()))
                : null;

        EqualityFormula[] equalities;
        if (middleFormula != null) {
            equalities = new EqualityFormula[3];
            equalities[0] = firstFormula;
            equalities[1] = middleFormula;
            equalities[2] = lastFormula;
        } else {
            equalities = new EqualityFormula[2];
            equalities[0] = firstFormula;
            equalities[1] = lastFormula;
        }

        assert (Util.checkEqualityChain(equalities));

        int numDisequalities = 0;
        for (Z3Proof child : subProofs) {
            if (Util.isNegativeLiteral(Util.getSingleLiteral(child.consequent
                    .transformToConsequentsForm())))
                numDisequalities++;
        }

        assert (numDisequalities <= 1);

        assert (firstFormula.getTerms().size() == 2);
        Term term1 = firstFormula.getTerms().get(0);
        assert (lastFormula.getTerms().size() == 2);
        Term term2 = lastFormula.getTerms().get(1);

        List<Term> newTerms = new ArrayList<Term>();
        newTerms.add(term1);
        newTerms.add(term2);

        Formula newFormula = null;
        try {
            newFormula = EqualityFormula
                    .create(newTerms, numDisequalities == 0)
                    .transformToConsequentsForm();
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Incomparable terms while creating transitivity proof.",
                    exc);
        }

        transformedSubProofs = new ArrayList<TransformedZ3Proof>(
                subProofs.size());
        if (subProofs.get(0) instanceof TransformedZ3Proof) {
            for (Z3Proof subProof : subProofs) {
                assert (subProof instanceof TransformedZ3Proof);
                transformedSubProofs.add((TransformedZ3Proof) subProof);
            }
        }
        Z3Proof result = (subProofs.get(0) instanceof TransformedZ3Proof) ? new TransformedZ3Proof(
                SExpressionConstants.TRANSITIVITY, transformedSubProofs,
                newFormula) : new Z3Proof(SExpressionConstants.TRANSITIVITY,
                subProofs, newFormula);

        // If we have three subproofs, we need to split them,
        // because conversion to local proof cannot deal with
        // three subproofs.
        assert (result.subProofs.size() <= 3);
        if (result.subProofs.size() == 3) {
            assert (result.proofType == SExpressionConstants.TRANSITIVITY);
            if (subProofs.get(0) instanceof TransformedZ3Proof) {
                transformedSubProofs = new ArrayList<TransformedZ3Proof>();
                for (Z3Proof proof : result.subProofs) {
                    assert (proof instanceof TransformedZ3Proof);
                    transformedSubProofs.add((TransformedZ3Proof) proof);
                }
            }
            Z3Proof intermediate = (subProofs.get(0) instanceof TransformedZ3Proof) ? TransformedZ3Proof
                    .createTransitivityProofForTransformedZ3Proofs(new ArrayList<TransformedZ3Proof>(
                            transformedSubProofs.subList(0, 2)))
                    : Z3Proof.createTransitivityProof(new ArrayList<Z3Proof>(
                            result.subProofs.subList(0, 2)));
            Z3Proof rest = result.subProofs.get(2);
            result.subProofs.clear();
            result.subProofs.add(intermediate);
            result.subProofs.add(rest);
        }

        return result;

    }

    /**
     * Creates a symmetry proof for the given premise.
     * 
     * @param premise
     *            must have a single literal as a consequence
     * @return a symmetry proof for the given premise.
     */
    public static Z3Proof createSymmetryProof(Z3Proof premise) {
        assert (premise.hasSingleLiteralConsequent());
        Formula literal = Util.makeLiteralPositive(Util
                .getSingleLiteral((premise.consequent
                        .transformToConsequentsForm())));
        assert (literal instanceof EqualityFormula);
        boolean equal = !Util.isNegativeLiteral(Util
                .getSingleLiteral(premise.consequent
                        .transformToConsequentsForm()));

        List<Term> terms = ((EqualityFormula) literal).getTerms();
        Collections.reverse(terms);
        Formula consequentFormula = null;
        try {
            consequentFormula = EqualityFormula.create(terms, equal);
            consequentFormula = consequentFormula.transformToConsequentsForm();
            assert (consequentFormula != null);
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Incomparable terms while creating symmetry proof.", exc);
        }
        List<Z3Proof> subproofs = new ArrayList<Z3Proof>();
        subproofs.add(premise);
        return new Z3Proof(SExpressionConstants.SYMMETRY, subproofs,
                consequentFormula);
    }

    /**
     * Checks if node is valid. Therefore, whether the given Subproofs together
     * produces the consequent of the node.
     * 
     * @return return true if node is valid
     */
    public boolean checkZ3ProofNode() {

        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type, "lib/z3/bin/z3");

        if (this.subProofs.size() > 0) {

            List<Formula> conjuncts = new ArrayList<Formula>();
            for (Z3Proof subProof : this.subProofs) {
                conjuncts.add(subProof.consequent);
            }
            conjuncts.add(NotFormula.create(this.consequent));
            Formula formulaToCheck = AndFormula.generate(conjuncts);

            String declarationStr = makeDeclarationsAndDefinitions(formulaToCheck);
            String formulaSmtStr = buildSMTDescription(declarationStr,
                    formulaToCheck.toString());

            z3.solve(formulaSmtStr);

            switch (z3.getState()) {
            case SMTSolver.UNSAT:
                break;
            case SMTSolver.SAT:
                System.out.println("Bad Node: " + this.id);
                throw new RuntimeException(
                        "Error while testing vality of Z3-node with Z3-solver: \n"
                                + "z3 tells us SAT, node is NOT valid.");
            default:
                System.out
                        .println("....Z3 OUTCOME ---->  UNKNOWN! CHECK ERROR STREAM.");
                throw (new RuntimeException(
                        "Z3 tells us UNKOWN STATE. CHECK ERROR STREAM."));
            }
        }
        return true;
    }

    /**
     * Checks recursive if node is valid. Therefore, whether the given Subproofs
     * together produces the consequent of the node. Also checks this property
     * recursive for every node of the subtree.
     * 
     * @return return true if node is valid
     */
    public boolean checkZ3ProofNodeRecursive() {

        long operationId = DagOperationManager.startDAGOperation();
        boolean result = this.checkZ3ProofNodeRecursiveRecursion(operationId);
        DagOperationManager.endDAGOperation(operationId);

        return result;
    }

    private boolean checkZ3ProofNodeRecursiveRecursion(long operationId) {
        if (this.wasVisitedByDAGOperation(operationId))
            return true;
        visitedByDAGOperation(operationId);
        if (this.subProofs.size() > 0)
            for (Z3Proof subProof : this.subProofs) {
                if (subProof.wasVisitedByDAGOperation(operationId))
                    continue;
                if (!subProof.checkZ3ProofNodeRecursiveRecursion(operationId))
                    return false;
            }
        return checkZ3ProofNode();
    }

    /**
     * Checks if proof is valid. Takes all asserted nodes (leafs) from a
     * partition, and checks if the original formula of this partition implies
     * these leafs. Does this for all partitions.
     * 
     * @param originalFormulas
     *            asserted formula for each partition
     * 
     * @return true if <code>Z3Proof</code> is valid
     */
    public boolean checkLeafsAgainstOriginalFormula(
            Map<Integer, Formula> originalFormulas) {
        Timer timer = new Timer();
        System.out.println("  Check proofs leafs to consequent...");
        timer.start();

        boolean result = true;
        Set<Z3Proof> leafes = this.allLeafs();
        assert (leafes.size() > 0);

        HashMap<Integer, ArrayList<Z3Proof>> partitionLeafMap = new HashMap<Integer, ArrayList<Z3Proof>>();
        List<Formula> globalLeafs = new ArrayList<Formula>();
        List<Formula> axiomsDisjuncts = new ArrayList<Formula>();
        for (Z3Proof leaf : leafes) {

            if (!leaf.proofType.equals(SExpressionConstants.HYPOTHESIS)) {

                assert (leaf.assertPartition != 0);

                ArrayList<Z3Proof> leafList = partitionLeafMap
                        .get(leaf.assertPartition);
                if (leafList == null) {
                    leafList = new ArrayList<Z3Proof>();
                    partitionLeafMap.put(leaf.assertPartition, leafList);
                }
                leafList.add(leaf);

                if (leaf.assertPartition == -1)
                    globalLeafs.add(NotFormula.create(leaf.consequent));
                if (leaf.axiom)
                    axiomsDisjuncts.add(NotFormula.create(leaf.consequent));
            }
        }

        // check each partition: phi_n /\ (~L1 \/ ~L2 \/ ... ) = UNSAT
        for (Map.Entry<Integer, ArrayList<Z3Proof>> entry : partitionLeafMap
                .entrySet()) {

            int partition = entry.getKey();
            if (partition != -1) {// not global

                List<Formula> disjuncts = new ArrayList<Formula>();
                for (Z3Proof leaf : entry.getValue())
                    disjuncts.add(NotFormula.create(leaf.consequent));

                if (globalLeafs != null)
                    disjuncts.addAll(globalLeafs);

                Formula leafFormula = OrFormula.generate(disjuncts);

                List<Formula> conjuncts = new ArrayList<Formula>();
                conjuncts.add(originalFormulas.get(partition));
                conjuncts.add(leafFormula);
                Formula formulaToCheck = AndFormula.generate(conjuncts);

                String declarationStr = makeDeclarationsAndDefinitions(formulaToCheck);
                String formulaSmtStr = buildSMTDescription(declarationStr,
                        formulaToCheck.toString());

                SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type,
                        "lib/z3/bin/z3");
                z3.solve(formulaSmtStr);

                switch (z3.getState()) {
                case SMTSolver.UNSAT:
                    break;
                case SMTSolver.SAT:
                    System.out
                            .println("Error while testing vality of Z3-proof with Z3-solver: \n"
                                    + "z3 tells us SAT, proof is NOT valid.");
                    System.out.println("Bad Node: " + this.id);
                    result = false;
                    break;
                default:
                    System.out
                            .println("Z3 tells us UNKOWN STATE. CHECK ERROR STREAM.");
                    result = false;
                }
            }
        }

        // check axioms: (~A1 \/ ~A2 \/ ... ) = UNSAT
        if (axiomsDisjuncts.size() > 0) {
            Formula formulaToCheck = OrFormula.generate(axiomsDisjuncts);

            String declarationStr = makeDeclarationsAndDefinitions(formulaToCheck);
            String formulaSmtStr = buildSMTDescription(declarationStr,
                    formulaToCheck.toString());

            SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type, "lib/z3/bin/z3");
            z3.solve(formulaSmtStr);

            switch (z3.getState()) {
            case SMTSolver.UNSAT:
                break;
            case SMTSolver.SAT:
                System.out
                        .println("Error while checking axioms with z3-solver Z3-solver: \n"
                                + "z3 tells us SAT. axioms are not valid");
                System.out.println("Bad Node: " + this.id);
                result = false;
                break;
            default:
                System.out
                        .println("Z3 tells us UNKOWN STATE. CHECK ERROR STREAM.");
                result = false;
            }
        }
        timer.stop();
        System.out.println("    Done. (" + timer + ")");
        timer.reset();

        return result;
    }

    /**
     * Checks if proof is valid. Takes all asserted nodes (leafs) of the proof,
     * and checks, whether all leafs together imply the consequence of the node.
     * 
     * @return true if <code>Z3Proof</code> is valid
     */

    public boolean checkProofLeafsToConsequent() {
        Timer timer = new Timer();
        System.out.println("  Check proofs leafs to consequent...");
        timer.start();
        Set<Z3Proof> leafs = this.allLeafs();

        // conjunction of all leafs and not the consequent -> UNSAT
        // L1 ^ L2 ^ L3 ^ ~C -> UNSAT

        boolean result = true;
        assert (leafs.size() > 0);
        List<Formula> conjuncts = new ArrayList<Formula>();
        for (Z3Proof leaf : leafs) {
            conjuncts.add(leaf.consequent);
        }
        conjuncts.add(NotFormula.create(this.consequent));
        Formula formulaToCheck = AndFormula.generate(conjuncts);

        String declarationStr = makeDeclarationsAndDefinitions(formulaToCheck);
        String formulaSmtStr = buildSMTDescription(declarationStr,
                formulaToCheck.toString());

        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type, "lib/z3/bin/z3");
        z3.solve(formulaSmtStr);

        switch (z3.getState()) {
        case SMTSolver.UNSAT:
            break;
        case SMTSolver.SAT:
            System.out
                    .println("Error while testing vality of Z3-node with Z3-solver: \n"
                            + "z3 tells us SAT, node is NOT valid.");
            System.out.println("Bad Node: " + this.id);
            result = false;
            break;
        default:
            System.out.println("Z3 tells us UNKOWN STATE. CHECK ERROR STREAM.");
            result = false;
        }

        timer.stop();
        System.out.println("    Done. (" + timer + ")");
        timer.reset();

        return result;
    }

    /**
     * Returns all leafs of the <code>Z3Proof</code>. A leaf is everything with
     * 0 subProofs.
     * 
     * @return all leafs of a <code>Z3Proof</code>
     */
    public Set<Z3Proof> allLeafs() {

        long operationId = DagOperationManager.startDAGOperation();
        Set<Z3Proof> leafs = new HashSet<Z3Proof>();
        this.allLeafsRecursion(leafs, operationId);
        DagOperationManager.endDAGOperation(operationId);

        return leafs;
    }

    private void allLeafsRecursion(Set<Z3Proof> set, long operationId) {
        if (this.wasVisitedByDAGOperation(operationId))
            return;
        visitedByDAGOperation(operationId);

        if (this.subProofs.size() > 0)
            for (Z3Proof subProof : this.subProofs) {
                subProof.allLeafsRecursion(set, operationId);
            }
        else {
            // assert (this.proofType.equals(SExpressionConstants.ASSERTED));
            set.add(this);
        }
    }

    /**
     * Writes the declarations of all domain variables, propositional variables,
     * uninterpreted functions, as well as the definition of all macros in
     * <code>formula</code>.
     * 
     * @param formula
     *            The formula for which to write the definitions.
     * @return the declaration
     */
    protected String makeDeclarationsAndDefinitions(Formula formula) {

        Set<SExpression> outputExpressions = new HashSet<SExpression>();

        for (PropositionalVariable var : formula.getPropositionalVariables())
            outputExpressions
                    .add(SExpression.makeDeclareFun((Token) var.toSmtlibV2(),
                            SExpressionConstants.BOOL_TYPE, 0));

        for (DomainVariable var : formula.getDomainVariables())
            outputExpressions.add(SExpression.makeDeclareFun(
                    (Token) var.toSmtlibV2(), SExpressionConstants.VALUE_TYPE,
                    0));

        for (UninterpretedFunction function : formula
                .getUninterpretedFunctions())
            outputExpressions.add(SExpression.makeDeclareFun(
                    function.getName(), function.getType(),
                    function.getNumParams()));

        for (FunctionMacro macro : this.consequent.getFunctionMacros())
            outputExpressions.add(macro.toSmtlibV2());

        String declarationsStr = "";
        for (SExpression declaration : outputExpressions)
            declarationsStr += declaration.toString();

        return declarationsStr;
    }

    /**
     * Creates an SMT description for a given formula
     * 
     * @param declarationStr
     *            declarations of the SMT description
     * @param formulaStr
     *            formula to be checked
     * @return SMT description
     * 
     */
    protected String buildSMTDescription(String declarationStr,
            String formulaStr) {
        String smtStr = "";

        smtStr += SExpressionConstants.SET_LOGIC_QF_UF.toString();
        smtStr += SExpressionConstants.DECLARE_SORT_VALUE.toString();

        smtStr += declarationStr;

        smtStr += "(assert" + formulaStr + ")";

        smtStr += SExpressionConstants.CHECK_SAT.toString();
        smtStr += SExpressionConstants.EXIT.toString();

        return smtStr;
    }

    public static int numInstances() {
        return Z3Proof.instanceCounter;
    }

    /**
     * 
     * @return the maximum "depth" of this proof. (length of the chain to a
     *         leaf)
     */
    public int depth() {
        Map<Z3Proof, Integer> map = new HashMap<Z3Proof, Integer>();
        return depthRecursion(map);
    }

    private int depthRecursion(Map<Z3Proof, Integer> map) {
        if (this.subProofs.isEmpty())
            return 1;

        if (map.containsKey(this))
            return map.get(this);
        int result = 0;
        for (Z3Proof child : subProofs) {
            int childDepth = child.depthRecursion(map);
            if (++childDepth > result)
                result = childDepth;
        }
        map.put(this, result);
        return result;
    }

    public Set<Z3Proof> getNodesWithConsequent(Formula consequent) {
        Set<Z3Proof> result = new HashSet<Z3Proof>();
        long operationId = DagOperationManager.startDAGOperation();
        this.getNodesWithConsequentRecursion(consequent, result, operationId);
        DagOperationManager.endDAGOperation(operationId);
        return result;
    }

    public void getNodesWithConsequentRecursion(Formula consequent,
            Set<Z3Proof> result, long operationId) {
        assert (result != null);
        if (wasVisitedByDAGOperation(operationId))
            return;
        visitedByDAGOperation(operationId);

        if (this.consequent.equals(consequent))
            result.add(this);

        for (Z3Proof child : subProofs)
            child.getNodesWithConsequentRecursion(consequent, result,
                    operationId);
    }

    /**
     * 
     * @return number of nodes in this proof
     */
    public int size() {
        return this.size(false);
    }

    /**
     * 
     * @param unwind
     *            if <code>true</code> unwind DAG into a tree
     * @return number of nodes in this proof, unwinding the DAG into a tree, if
     *         <code>unwind</code> is <code>true</code>.
     */
    public int size(boolean unwind) {

        int result = 1;
        if (unwind) {
            for (Z3Proof child : subProofs)
                result += child.size();
            return result;
        } else {

            long operationId = DagOperationManager.startDAGOperation();
            result = this.sizeRecursion(operationId);
            DagOperationManager.endDAGOperation(operationId);

            return result;
        }
    }

    private int sizeRecursion(long operationId) {
        int result = 1;
        if (this.wasVisitedByDAGOperation(operationId))
            return 0;
        visitedByDAGOperation(operationId);
        for (Z3Proof child : subProofs)
            result += child.sizeRecursion(operationId);
        return result;
    }

    /**
     * Recursively computes the parents in the proof, starting from
     * <code>this</code> downwards.
     * 
     * 
     */
    public void computeParents() {
        long operationId = DagOperationManager.startDAGOperation();
        this.computeParentsRecursion(operationId);
        DagOperationManager.endDAGOperation(operationId);
    }

    private void computeParentsRecursion(long operationId) {
        if (this.wasVisitedByDAGOperation(operationId))
            return;
        visitedByDAGOperation(operationId);

        for (Z3Proof child : subProofs) {
            child.addParent(this);
            child.computeParentsRecursion(operationId);
        }
        return;
    }

    /**
     * Walks through the set <code>localNodes</code> starting from
     * <code>this</code> and duplicates all parents that are contained in
     * <code>toDuplicate</code>.
     * 
     * @param toDuplicate
     *            nodes that should be duplicated
     * @param localNodes
     *            nodes making up the paths we care about.
     * @return a map from old to new nodes
     */
    public Map<Z3Proof, Z3Proof> duplicate(Set<Z3Proof> toDuplicate,
            Set<Z3Proof> localNodes) {
        long operationId = DagOperationManager.startDAGOperation();
        Map<Z3Proof, Z3Proof> duplicates = new HashMap<Z3Proof, Z3Proof>();
        duplicate(operationId, toDuplicate, duplicates, localNodes);
        DagOperationManager.endDAGOperation(operationId);
        assert (duplicates.size() == toDuplicate.size());
        return duplicates;
    }

    private void duplicate(long operationId, Set<Z3Proof> toDuplicate,
            Map<Z3Proof, Z3Proof> duplicates, Set<Z3Proof> localNodes) {
        assert (toDuplicate != null);
        assert (duplicates != null);
        assert (Collections.disjoint(toDuplicate, localNodes));

        if (this.wasVisitedByDAGOperation(operationId))
            return;
        visitedByDAGOperation(operationId);

        if (duplicates.containsKey(this))
            return;

        if (localNodes.contains(this)) {
            for (Z3Proof child : this.subProofs)
                child.duplicate(operationId, toDuplicate, duplicates,
                        localNodes);
            return;
        }

        if (!toDuplicate.contains(this))
            // neither a local node, nor one to duplicate.
            // this is not on the path that we are interested in.
            // ignoring it
            return;

        assert (toDuplicate.contains(this));

        Z3Proof duplicate = new Z3Proof(this.proofType, new ArrayList<Z3Proof>(
                0), this.consequent.deepFormulaCopy());
        duplicate.takeValuesFrom(this);
        duplicates.put(this, duplicate);

        List<Z3Proof> duplicateSubProofs = new ArrayList<Z3Proof>(
                this.subProofs.size());
        for (Z3Proof subProof : this.subProofs) {
            if (!toDuplicate.contains(subProof))
                duplicateSubProofs.add(subProof);
            else {
                subProof.duplicate(operationId, toDuplicate, duplicates,
                        localNodes);
                assert (duplicates.containsKey(subProof));
                duplicateSubProofs.add(duplicates.get(subProof));
            }
        }
        duplicate.subProofs = duplicateSubProofs; // must be overwritten now

        duplicate.parents = new HashSet<SoftReferenceWithEquality<Z3Proof>>();
        for (SoftReferenceWithEquality<Z3Proof> parentRef : this.parents) {
            Z3Proof parent = parentRef.get();
            assert (parent != null);
            SoftReferenceWithEquality<Z3Proof> newParentRef = null;
            if (toDuplicate.contains(parent)) {
                if (!duplicates.containsKey(parent))
                    parent.duplicate(operationId, toDuplicate, duplicates,
                            localNodes);
                assert (duplicates.containsKey(parent));
                assert (duplicates.get(parent) != null);
                newParentRef = new SoftReferenceWithEquality<Z3Proof>(
                        duplicates.get(parent));
            } else {
                if (localNodes.contains(parent))
                    newParentRef = new SoftReferenceWithEquality<Z3Proof>(
                            parent);
            }
            if (newParentRef != null) {
                assert (newParentRef.get() != null);
                duplicate.parents.add(newParentRef);
            }
        }
    }

    /**
     * 
     * @param target
     * @return all the nodes on paths to the target, including the target
     *         itself.
     */
    public Set<Z3Proof> nodesOnPathTo(Z3Proof target) {
        long operationId = DagOperationManager.startDAGOperation();
        Set<Z3Proof> result = new HashSet<Z3Proof>();
        nodesOnPathToRecursion(operationId, target, result);
        DagOperationManager.endDAGOperation(operationId);
        return result;
    }

    private boolean nodesOnPathToRecursion(long operationId, Z3Proof target,
            Set<Z3Proof> result) {
        assert (result != null);

        if (this == target) {
            result.add(this);
            return true;
        }
        if (wasVisitedByDAGOperation(operationId))
            return false;
        visitedByDAGOperation(operationId);

        boolean flag = false;
        for (Z3Proof child : subProofs) {
            if (result.contains(child)) {
                result.add(this);
                flag = true;
                continue;
            }
            if (child.nodesOnPathToRecursion(operationId, target, result)) {
                result.add(this);
                flag = true;
            }
        }
        return flag;
    }

    /**
     * 
     * @param target
     * @return all the nodes on paths to a hypothesis with the given formula,
     *         excluding the actual hypothesis.
     */
    public Set<Z3Proof> nodesOnPathToHypothesisFormula(Formula target) {
        long operationId = DagOperationManager.startDAGOperation();
        Set<Z3Proof> result = new HashSet<Z3Proof>();
        nodesOnPathToHypothesisFormulaRecursion(operationId, target, result);
        DagOperationManager.endDAGOperation(operationId);
        return result;
    }

    private boolean nodesOnPathToHypothesisFormulaRecursion(long operationId,
            Formula target, Set<Z3Proof> result) {
        assert (result != null);

        if (this.consequent.equals(target))
            return true;

        if (this.wasVisitedByDAGOperation(operationId))
            return false;

        visitedByDAGOperation(operationId);

        boolean flag = false;
        for (Z3Proof child : subProofs) {
            if (result.contains(child)) {
                result.add(this);
                flag = true;
                continue;
            }
            if (child.nodesOnPathToHypothesisFormulaRecursion(operationId,
                    target, result)) {
                result.add(this);
                flag = true;
            }
        }
        return flag;
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(SMTLibObject o) {
        return this.toString().compareTo(o.toString());
    }

    /**
     * @return the <code>assertPartition</code>
     */
    public int getAssertPartitionOfThisNode() {
        assert (assertPartition > 0 || !this.proofType
                .equals(SExpressionConstants.ASSERTED));
        return assertPartition;
    }

    /**
     * Necessary for restore after load from cache. Do not tamper with the
     * instance counter otherwise!
     * 
     * @param value
     *            the new value for the instance counter
     */
    public static void setInstanceCounter(int value) {
        Z3Proof.instanceCounter = value;
    }

    /**
     * 
     * @return the current value of the instance counter
     */
    public static int getInstanceCounter() {
        return Z3Proof.instanceCounter;
    }

    /**
     * 
     * @return <code>true</code> iff this proof object is a leaf.
     *         <code>false</code> otherwise.
     */
    public boolean isLeaf() {
        return subProofs.isEmpty();
    }

    /**
     * @return <code>true</code> iff this is a hypothesis node.
     */
    public boolean isHypothesis() {
        return proofType.equals(SExpressionConstants.HYPOTHESIS);
    }

    /**
     * Adds missing reflexivity proofs to a monotonicity proof. Does nothing on
     * other proof types.
     * 
     * Also performs sanity checks. E.g. if the subproofs actually proof what
     * they are supposed to prove.
     * 
     */
    protected void addMissingReflexivityProofs() {
        if (!this.proofType.equals(SExpressionConstants.MONOTONICITY))
            return;
        assert (this.hasSingleLiteralConsequent());
        assert (Util.getSingleLiteral(this.consequent) instanceof EqualityFormula);
        EqualityFormula consequentEq = (EqualityFormula) Util
                .getSingleLiteral(this.consequent);
        assert (consequentEq.getTerms().size() == 2);
        List<Term> leftTerms = new ArrayList<Term>();
        List<Term> rightTerms = new ArrayList<Term>();

        if (consequentEq.getTerms().get(0) instanceof UninterpretedFunctionInstance) {
            assert (consequentEq.getTerms().get(1) instanceof UninterpretedFunctionInstance);
            UninterpretedFunctionInstance leftFunctionInstance = (UninterpretedFunctionInstance) consequentEq
                    .getTerms().get(0);
            UninterpretedFunctionInstance rightFunctionInstance = (UninterpretedFunctionInstance) consequentEq
                    .getTerms().get(1);
            assert (leftFunctionInstance.getFunction()
                    .equals(rightFunctionInstance.getFunction()));
            assert (leftFunctionInstance.getParameters().size() == rightFunctionInstance
                    .getParameters().size());
            leftTerms.addAll(leftFunctionInstance.getParameters());
            rightTerms.addAll(rightFunctionInstance.getParameters());

        } else {

            Formula leftFormula = null;
            if (consequentEq.getTerms().get(0) instanceof FormulaTerm)
                leftFormula = ((FormulaTerm) consequentEq.getTerms().get(0))
                        .getFormula();
            else {
                assert (consequentEq.getTerms().get(0) instanceof PropositionalTerm);
                leftFormula = ((PropositionalTerm) consequentEq.getTerms().get(
                        0));
            }
            assert (leftFormula != null);

            Formula rightFormula = null;
            if (consequentEq.getTerms().get(1) instanceof FormulaTerm)
                rightFormula = ((FormulaTerm) consequentEq.getTerms().get(1))
                        .getFormula();
            else {
                assert (consequentEq.getTerms().get(1) instanceof PropositionalTerm);
                rightFormula = ((PropositionalTerm) consequentEq.getTerms()
                        .get(1));
            }
            assert (rightFormula != null);

            if (leftFormula instanceof UninterpretedPredicateInstance) {
                assert (rightFormula instanceof UninterpretedPredicateInstance);
                UninterpretedPredicateInstance leftPredicateInstance = (UninterpretedPredicateInstance) leftFormula;
                UninterpretedPredicateInstance rightPredicateInstance = (UninterpretedPredicateInstance) rightFormula;
                assert (leftPredicateInstance.getFunction()
                        .equals(rightPredicateInstance.getFunction()));
                assert (leftPredicateInstance.getParameters().size() == rightPredicateInstance
                        .getParameters().size());
                leftTerms.addAll(leftPredicateInstance.getParameters());
                rightTerms.addAll(rightPredicateInstance.getParameters());
            } else if (leftFormula instanceof DomainEq) {
                assert (rightFormula instanceof DomainEq);
                DomainEq leftEq = (DomainEq) leftFormula;
                DomainEq rightEq = (DomainEq) rightFormula;

                assert (leftEq.getTerms().size() == 2);
                assert (rightEq.getTerms().size() == 2);
                leftTerms.add(leftEq.getTerms().get(0));
                leftTerms.add(leftEq.getTerms().get(1));
                rightTerms.add(rightEq.getTerms().get(0));
                rightTerms.add(rightEq.getTerms().get(1));

            } else
                throw new RuntimeException(
                        "Unexpected type of monotonicity proof. ID: " + this.id);
        }

        assert (leftTerms.size() > 0);
        assert (rightTerms.size() > 0);
        assert (leftTerms.size() == rightTerms.size());
        assert (leftTerms.size() >= subProofs.size());

        for (int count = 0; count < leftTerms.size(); count++) {
            Term leftTerm = leftTerms.get(count);
            Term rightTerm = rightTerms.get(count);
            Z3Proof subProof = subProofs.size() > count ? subProofs.get(count)
                    : null;
            boolean missingSubProof = (subProof == null);
            if (subProof != null) {
                assert (Util.getSingleLiteral(subProof.consequent) instanceof EqualityFormula);
                EqualityFormula subEq = (EqualityFormula) Util
                        .getSingleLiteral(subProof.consequent);
                assert (subEq.getTerms().size() == 2);
                if (!subEq.getTerms().get(0).equals(leftTerm))
                    missingSubProof = true;
                if (!subEq.getTerms().get(1).equals(rightTerm))
                    missingSubProof = true;
            }
            if (missingSubProof) {
                if (!leftTerm.equals(rightTerm))
                    assert (false);

                Z3Proof missingProof = TransformedZ3Proof
                        .createReflexivityProof(leftTerm);
                List<Z3Proof> newSubProofs = new ArrayList<Z3Proof>();
                newSubProofs.addAll(subProofs.subList(0, count));
                newSubProofs.add(missingProof);
                newSubProofs.addAll(subProofs.subList(count, subProofs.size()));
                this.subProofs = newSubProofs;
            }
        }

    }

    /**
     * 
     * @param formula
     *            the formula to look for
     * @return the set of all proof nodes in this proof (and transitive
     *         subproofs) which have an IFF node as their consequent where one
     *         of the sides of the IFF equals the given formula.
     */
    public Set<Z3Proof> findIffNodes(Formula formula) {
        Set<Z3Proof> result = new HashSet<Z3Proof>();
        long operationId = DagOperationManager.startDAGOperation();
        findIffNodesRecursion(operationId, formula, result);
        DagOperationManager.endDAGOperation(operationId);
        return result;
    }

    private void findIffNodesRecursion(long operationId, Formula formula,
            Set<Z3Proof> result) {
        if (this.wasVisitedByDAGOperation(operationId))
            return;
        this.visitedByDAGOperation(operationId);

        if (this.consequent instanceof PropositionalEq) {
            PropositionalEq consequentEq = (PropositionalEq) this.consequent;
            if (consequentEq.getTerms().size() == 2) {
                assert (consequentEq.getTerms().get(0) instanceof PropositionalTerm);
                assert (consequentEq.getTerms().get(1) instanceof PropositionalTerm);
                PropositionalTerm term1 = (PropositionalTerm) consequentEq
                        .getTerms().get(0);
                PropositionalTerm term2 = (PropositionalTerm) consequentEq
                        .getTerms().get(1);
                PropositionalTerm positiveTerm = FormulaTerm.create((Util
                        .makeLiteralPositive(formula)));
                PropositionalTerm negativeTerm = FormulaTerm
                        .create(NotFormula.create(Util
                                .makeLiteralPositive(formula)));
                if (term1.equals(formula) || term2.equals(formula)
                        || term1.equals(positiveTerm)
                        || term1.equals(negativeTerm)
                        || term2.equals(positiveTerm)
                        || term2.equals(negativeTerm))
                    result.add(this);
            }
        }

        for (Z3Proof child : subProofs) {
            child.findIffNodesRecursion(operationId, formula, result);
        }
    }

}
