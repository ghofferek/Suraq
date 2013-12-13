/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util.chain;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import at.iaik.suraq.proof.VeriTToken;
import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.util.CongruenceClosure;
import at.iaik.suraq.util.Justification;
import at.iaik.suraq.util.Util;
import at.iaik.suraq.util.graph.Graph;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TransitivityCongruenceChain {

    /**
     * Counter to give unique names to proof nodes created in this class.
     */
    private static int proofNodeCounter = 1;

    /**
     * The starting point of the chain.
     */
    private final TransitivityCongruenceChainElement start;

    /**
     * The target of the chain.
     */
    private DomainTerm target;

    /**
     * The proof to which this will later be exported, or <code>null</code>.
     */
    private final VeritProof proof;

    /**
     * Creates a chain for the given (axiomatic) proof node.
     * 
     * @param node
     * @return the chain constructed for the given <code>node</code>.
     */
    public static TransitivityCongruenceChain create(VeritProofNode node) {
        assert (node != null);
        assert (node.isAxiom());
        assert (node.checkProofNode());

        Formula impliedLiteral = Util.getImpliedLiteral(node
                .getLiteralConclusions());
        assert (Util.isLiteral(impliedLiteral));
        assert (!Util.isNegativeLiteral(impliedLiteral));
        assert (impliedLiteral instanceof DomainEq);
        assert (((DomainEq) impliedLiteral).isEqual());
        assert (((DomainEq) impliedLiteral).getTerms().size() == 2);
        assert (((DomainEq) impliedLiteral).getTerms().get(0) instanceof DomainTerm);
        assert (((DomainEq) impliedLiteral).getTerms().get(1) instanceof DomainTerm);

        List<DomainEq> equalities = new ArrayList<DomainEq>();
        for (Formula literal : node.getLiteralConclusions()) {
            if (!Util.isNegativeLiteral(literal)) {
                assert (Util.isAtom(literal));
                continue;
            }
            Formula positiveLiteral = Util.makeLiteralPositive(literal);
            assert (positiveLiteral instanceof DomainEq);
            equalities.add((DomainEq) positiveLiteral);
        }

        return TransitivityCongruenceChain.create((DomainEq) impliedLiteral,
                equalities, node);
    }

    /**
     * Creates a chain for the given <code>impliedLiteral</code> from the given
     * <code>otherLiterals</code>.
     * 
     * @param impliedLiteral
     * @param implyingLiterals
     * @return
     */
    public static TransitivityCongruenceChain create(DomainEq impliedLiteral,
            List<DomainEq> implyingLiterals, VeritProofNode node) {
        assert (impliedLiteral != null);
        assert (implyingLiterals != null);
        assert (!implyingLiterals.isEmpty());
        assert (Util.isLiteral(impliedLiteral));
        assert (!Util.isNegativeLiteral(impliedLiteral));
        assert (node == null ? true : node.checkProofNode());
        assert (CongruenceClosure.checkLiteralImplication(implyingLiterals,
                impliedLiteral));

        Graph<DomainTerm, Justification> graph = new Graph<DomainTerm, Justification>(
                true);
        for (DomainEq literal : implyingLiterals) {
            assert (literal.isEqual());
            assert (literal.getTerms().size() == 2);
            assert (literal.getTerms().get(0) instanceof DomainTerm);
            assert (literal.getTerms().get(1) instanceof DomainTerm);

            Justification justification = new Justification(literal);
            graph.addEdge((DomainTerm) literal.getTerms().get(0),
                    (DomainTerm) literal.getTerms().get(1), justification);
            graph.addEdge((DomainTerm) literal.getTerms().get(1),
                    (DomainTerm) literal.getTerms().get(0), justification);

            Set<DomainTerm> additionalTerms = new HashSet<DomainTerm>();
            if (literal.getTerms().get(0) instanceof UninterpretedFunctionInstance) {
                additionalTerms.addAll(((UninterpretedFunctionInstance) literal
                        .getTerms().get(0)).getSubTerms());
            }
            if (literal.getTerms().get(1) instanceof UninterpretedFunctionInstance) {
                additionalTerms.addAll(((UninterpretedFunctionInstance) literal
                        .getTerms().get(1)).getSubTerms());
            }
            for (DomainTerm term : additionalTerms)
                graph.addNode(term);
        }
        assert (impliedLiteral.getTerms().size() == 2);
        assert (impliedLiteral.getTerms().get(0) instanceof DomainTerm);
        assert (impliedLiteral.getTerms().get(1) instanceof DomainTerm);
        graph.addNode((DomainTerm) impliedLiteral.getTerms().get(0));
        graph.addNode((DomainTerm) impliedLiteral.getTerms().get(1));
        boolean addedSomething = true;

        List<Justification> path = graph.findPath((DomainTerm) impliedLiteral
                .getTerms().get(0),
                (DomainTerm) impliedLiteral.getTerms().get(1));
        while (path == null) {
            assert (addedSomething);
            addedSomething = false;
            Set<DomainTerm> nodes = graph.getNodes();
            for (DomainTerm term1 : nodes) {
                if (!(term1 instanceof UninterpretedFunctionInstance))
                    continue;
                for (DomainTerm term2 : nodes) {
                    if (!(term2 instanceof UninterpretedFunctionInstance))
                        continue;
                    if (term1 == term2)
                        continue;
                    if (!((UninterpretedFunctionInstance) term1).getFunction()
                            .equals(((UninterpretedFunctionInstance) term2)
                                    .getFunction()))
                        continue;
                    if (graph.findPath(term1, term2) != null)
                        continue;
                    List<TransitivityCongruenceChain> localJustification = new ArrayList<TransitivityCongruenceChain>();
                    for (int count = 0; count < ((UninterpretedFunctionInstance) term1)
                            .getParameters().size(); count++) {
                        List<Justification> localPath = graph.findPath(
                                ((UninterpretedFunctionInstance) term1)
                                        .getParameters().get(count),
                                ((UninterpretedFunctionInstance) term2)
                                        .getParameters().get(count));
                        if (localPath == null) {
                            localJustification = null;
                            break;
                        }
                        localJustification.add(new TransitivityCongruenceChain(
                                ((UninterpretedFunctionInstance) term1)
                                        .getParameters().get(count),
                                ((UninterpretedFunctionInstance) term2)
                                        .getParameters().get(count), localPath,
                                node.getProof()));
                    }
                    if (localJustification != null) {
                        Justification completeLocalJustification = new Justification(
                                localJustification);
                        graph.addEdge(term1, term2, completeLocalJustification);
                        graph.addEdge(term2, term1,
                                completeLocalJustification.reverse());
                        addedSomething = true;
                    }
                }
            }
            path = graph.findPath(
                    (DomainTerm) impliedLiteral.getTerms().get(0),
                    (DomainTerm) impliedLiteral.getTerms().get(1));
        }
        assert (path != null);

        TransitivityCongruenceChain chain = new TransitivityCongruenceChain(
                (DomainTerm) impliedLiteral.getTerms().get(0),
                (DomainTerm) impliedLiteral.getTerms().get(1), path, node);
        return chain;
    }

    /**
     * 
     * Constructs a new <code>TransitivityCongruenceChain</code>.
     * 
     * @param start
     *            the start term of the chain
     * @param target
     *            the target term of the chain
     * @param node
     *            the proof node corresponding to this chain (for
     *            <code>proof</code> and <code>targerLiterals</code>. Can be
     *            <code>null</code>.
     */
    private TransitivityCongruenceChain(DomainTerm start, DomainTerm target,
            VeritProofNode node) {
        assert (start != null);
        assert (target != null);
        this.start = new TransitivityCongruenceChainElement(start);
        this.target = target;
        if (node != null) {
            this.proof = node.getProof();
        } else {
            this.proof = null;
        }
    }

    /**
     * 
     * Constructs a new <code>TransitivityCongruenceChain</code>.
     * 
     * @param start
     * @param target
     * @param proof
     */
    private TransitivityCongruenceChain(DomainTerm start, DomainTerm target,
            VeritProof proof) {
        assert (start != null);
        assert (target != null);
        this.start = new TransitivityCongruenceChainElement(start);
        this.target = target;
        this.proof = proof;
    }

    /**
     * 
     * Constructs a new <code>TransitivityCongruenceChain</code>. This
     * constructor is used to split a chain during creation of a colorable
     * proof.
     * 
     * @param start
     * @param target
     * @param proof
     */
    private TransitivityCongruenceChain(
            TransitivityCongruenceChainElement start, DomainTerm target,
            VeritProof proof) {
        this.start = start;
        this.proof = proof;
        this.target = target;
    }

    /**
     * 
     * Constructs a new <code>TransitivityCongruenceChain</code> which consists
     * just of one reflexivity over <code>term</code>.
     * 
     * @param reflexiveTerm
     * @param proof
     */
    private TransitivityCongruenceChain(DomainTerm reflexiveTerm,
            VeritProof proof) {
        this.start = new TransitivityCongruenceChainElement(reflexiveTerm);
        this.target = reflexiveTerm;
        this.proof = proof;
        this.start.attachReflexivity();
        assert (this.isComplete());
    }

    /**
     * Constructs a new <code>TransitivityCongruenceChain</code> from a list of
     * justifications.
     * 
     * @param start
     * @param end
     * @param path
     * @param node
     */
    private TransitivityCongruenceChain(DomainTerm start, DomainTerm end,
            List<Justification> path, VeritProofNode node) {
        this(start, end, path, node == null ? null : node.getProof());
    }

    /**
     * Constructs a new <code>TransitivityCongruenceChain</code> from a list of
     * justifications.
     * 
     * @param start
     * @param end
     * @param path
     * @param proof
     */
    private TransitivityCongruenceChain(DomainTerm start, DomainTerm end,
            List<Justification> path, VeritProof proof) {
        assert (path != null);
        assert (start != null);
        assert (end != null);
        this.start = new TransitivityCongruenceChainElement(start);
        this.target = end;
        this.proof = proof;

        for (Justification justification : path) {
            assert (justification != null);
            if (justification.isEqualityJustification()) {
                boolean attached = this.getEnd().tryAttach(
                        justification.getEqualityJustification());
                assert (attached);
                continue;
            }
            if (justification.isCongruenceJustification()) {
                boolean attached = this.getEnd().tryAttach(
                        justification.getCongruenceJustification());
                assert (attached);
                continue;
            }
            assert (false);
        }
        assert (this.isComplete());
    }

    /**
     * 
     * @return a proof node that proofs the targetLiterals, and is split in
     *         colorable subproofs.
     */
    public VeritProofNode toColorableProof() {
        assert (proof != null);

        this.splitUncolorableCongruenceLinks();

        int startPartition = this.getStartPartition();
        int endPartition = this.getEndPartition();
        assert (startPartition == endPartition || startPartition == -1 || endPartition == -1);

        TransitivityCongruenceChainElement currentElement = this.start;
        TransitivityCongruenceChain firstLocalChunk = null;
        TransitivityCongruenceChain chainWithGlobalEnds = null;
        TransitivityCongruenceChain lastLocalChunk = null;

        // Create chain for first local chunk
        if (startPartition > 0) {
            List<Justification> path = new ArrayList<Justification>();
            DomainTerm currentTerm = null;
            while (currentElement.getTermPartition() == startPartition
                    || currentElement.getTermPartition() == -1) {
                path.add(currentElement.getJustficiation());
                currentTerm = currentElement.getTerm();
                currentElement = currentElement.getNext();
                if (currentElement == null)
                    return this.toColorableProofBaseCase();
            }
            path.remove(path.size() - 1);
            firstLocalChunk = new TransitivityCongruenceChain(
                    this.start.getTerm(), currentTerm, path, this.proof);
            currentElement = this.getPredecessor(currentElement);
            assert (currentElement.getTermPartition() == -1);
        }

        // Create chain for last local chunk
        TransitivityCongruenceChainElement globalStart = currentElement;
        TransitivityCongruenceChainElement globalEnd = null;
        assert (globalStart.getTermPartition() == -1);
        if (endPartition > 0) {
            currentElement = this.getEnd();
            assert (currentElement.getNext() == null);
            currentElement = this.getPredecessor(currentElement);
            assert (currentElement != null);
            List<Justification> path = new ArrayList<Justification>();
            while (currentElement.getTermPartition() == endPartition
                    || currentElement.getTermPartition() == -1) {
                path.add(0, currentElement.getJustficiation());
                if (currentElement == this.start)
                    return this.toColorableProofBaseCase();
                currentElement = this.getPredecessor(currentElement);
            }
            assert (!path.isEmpty());
            currentElement = currentElement.getNext();
            assert (currentElement.getTermPartition() == -1);
            lastLocalChunk = new TransitivityCongruenceChain(
                    currentElement.getTerm(), this.getEndTerm(), path,
                    this.proof);
            globalEnd = currentElement;
        }
        if (globalEnd == null)
            globalEnd = this.getEnd();
        assert (globalEnd.getTermPartition() == -1);

        assert (globalStart != globalEnd);

        // Create chain with two global ends
        currentElement = globalStart;
        List<Justification> path = new ArrayList<Justification>();
        while (currentElement != globalEnd) {
            path.add(currentElement.getJustficiation());
            currentElement = currentElement.getNext();
            assert (currentElement != null);
        }
        assert (currentElement == globalEnd);
        chainWithGlobalEnds = new TransitivityCongruenceChain(
                globalStart.getTerm(), globalEnd.getTerm(), path, this.proof);

        VeritProofNode proofForMidSection = chainWithGlobalEnds
                .chainWithGlobalEndsToColorableProof();

        if (firstLocalChunk == null && lastLocalChunk == null)
            return proofForMidSection;

        // Create "shortcut"-literal for mid section
        List<DomainTerm> terms = new ArrayList<DomainTerm>(2);
        terms.add(globalStart.getTerm());
        terms.add(globalEnd.getTerm());
        DomainEq shortcutLiteral = DomainEq.create(terms, true);

        // Create conclusions for new node (leaf with firstChunk, shortcut,
        // lastChunk)
        List<Formula> conclusions = new ArrayList<Formula>();
        if (firstLocalChunk != null)
            conclusions.addAll(Util.invertAllLiterals(firstLocalChunk
                    .usedLiterals()));
        conclusions.add(Util.invertLiteral(shortcutLiteral));
        if (lastLocalChunk != null)
            conclusions.addAll(Util.invertAllLiterals(lastLocalChunk
                    .usedLiterals()));
        List<DomainTerm> impliedLiteralTerms = new ArrayList<DomainTerm>(2);
        impliedLiteralTerms
                .add((DomainTerm) (firstLocalChunk != null ? firstLocalChunk
                        .getStart().getTerm() : shortcutLiteral.getTerms().get(
                        0)));
        impliedLiteralTerms
                .add((DomainTerm) (lastLocalChunk != null ? lastLocalChunk
                        .getEndTerm() : shortcutLiteral.getTerms().get(1)));
        DomainEq impliedLiteral = DomainEq.create(impliedLiteralTerms, true);
        conclusions.add(impliedLiteral);
        VeritProofNode firstShortcutLast = this.proof.addProofNode("fsl_"
                + TransitivityCongruenceChain.proofNodeCounter++,
                VeriTToken.TRANS_CONGR, conclusions, null, null, false);

        // Create the final result
        List<VeritProofNode> resultSubProofs = new ArrayList<VeritProofNode>(2);
        resultSubProofs.add(firstShortcutLast);
        resultSubProofs.add(proofForMidSection);
        List<Formula> resultConclusions = new ArrayList<Formula>();
        for (Formula literal : firstShortcutLast.getLiteralConclusions()) {
            if (!resultConclusions.contains(literal))
                resultConclusions.add(literal);
        }
        for (Formula literal : proofForMidSection.getLiteralConclusions()) {
            if (!resultConclusions.contains(literal))
                resultConclusions.add(literal);
        }
        while (resultConclusions.contains(shortcutLiteral))
            resultConclusions.remove(shortcutLiteral);
        while (resultConclusions.contains(Util.invertLiteral(shortcutLiteral)))
            resultConclusions.remove(Util.invertLiteral(shortcutLiteral));

        VeritProofNode result = this.proof.addProofNode("split_"
                + TransitivityCongruenceChain.proofNodeCounter++,
                VeriTToken.RESOLUTION, resultConclusions, resultSubProofs,
                null, false);

        return result;
    }

    /**
     * Call only on chains that span only one partition!
     * 
     * @return a (colorable) VeritProofNode for this chain.
     */
    private VeritProofNode toColorableProofBaseCase() {
        assert (this.proof != null);
        Set<Integer> partitions = this.getPartitionsFromSymbols();
        partitions.remove(-1);

        // Create implied Literal
        List<DomainTerm> terms = new ArrayList<DomainTerm>(2);
        terms.add(this.getStart().getTerm());
        terms.add(this.getEndTerm());
        DomainEq impliedLiteral = DomainEq.create(terms, true);

        if (partitions.size() <= 1) {
            Set<Formula> usedLiterals = this.usedLiterals();
            List<Formula> conclusions = new ArrayList<Formula>(
                    usedLiterals.size() + 1);
            conclusions.addAll(Util.invertAllLiterals(usedLiterals));
            conclusions.add(impliedLiteral);
            VeritProofNode result = proof.addProofNode("col_"
                    + TransitivityCongruenceChain.proofNodeCounter++,
                    VeriTToken.TRANS_CONGR, conclusions, null, null, false);
            return result;
        } else {
            // Special case: at least one chain link has a congruence
            // justification for a local function over another partition
            assert (this.length() >= 2);

            List<VeritProofNode> congruences = new ArrayList<VeritProofNode>();
            List<Formula> conclusions = new ArrayList<Formula>();
            TransitivityCongruenceChainElement current = this.start;
            partitions = new TreeSet<Integer>();
            assert (current != null);

            while (current != null) {

                // Collect literals for colorable conclusion
                // For congruences over other partitions, collect colorable
                // subproofs.
                if (current.isCongruenceOfLocalFunctionOverOtherPartition()
                        || current.isCongruenceOverOtherPartition(partitions)) {
                    assert (current.getCongruenceJustification() != null);
                    assert (current.getTerm() != null);
                    assert (current.getTerm() instanceof UninterpretedFunctionInstance);
                    assert (current.getNext().getTerm() != null);
                    assert (current.getNext().getTerm() instanceof UninterpretedFunctionInstance);
                    VeritProofNode congruence = TransitivityCongruenceChain
                            .congruenceJustificationToColorableProof(current
                                    .getCongruenceJustification(),
                                    (UninterpretedFunctionInstance) current
                                            .getTerm(),
                                    (UninterpretedFunctionInstance) current
                                            .getNext().getTerm(), this.proof);
                    congruences.add(congruence);
                    assert (Util.findPositiveLiteral(congruence
                            .getLiteralConclusions()) != null);

                    Formula literal = Util.invertLiteral(Util
                            .findPositiveLiteral(congruence
                                    .getLiteralConclusions()));
                    partitions.addAll(literal.getPartitionsFromSymbols());
                    partitions.remove(-1);
                    assert (partitions.size() <= 1);
                    conclusions.add(literal);
                } else {
                    List<Formula> literals = Util.invertAllLiterals(current
                            .usedLiterals());
                    for (Formula literal : literals) {
                        partitions.addAll(literal.getPartitionsFromSymbols());
                        partitions.remove(-1);
                        assert (partitions.size() <= 1);
                        conclusions.add(literal);
                    }
                }
                current = current.getNext();
            }

            // Construct colorable leaf with all literals except the "details"
            // of the congruences across other partitions

            // First, we need to add the implied literal
            conclusions.add(impliedLiteral);

            // Now we actually construct the leaf
            VeritProofNode currentNode = proof.addProofNode(
                    proof.freshNodeName("col_", ""), VeriTToken.TRANS_CONGR,
                    conclusions, null, null, false);

            // Add resolution steps to get the final conclusion
            for (VeritProofNode currentCongruence : congruences) {
                List<VeritProofNode> subProofs = new ArrayList<VeritProofNode>(
                        2);
                subProofs.add(currentNode);
                subProofs.add(currentCongruence);
                Formula resolvingLiteral = Util.findResolvingLiteral(subProofs);
                List<Formula> currentConclusions = new ArrayList<Formula>();
                currentConclusions.addAll(subProofs.get(0)
                        .getLiteralConclusions());
                currentConclusions.addAll(subProofs.get(1)
                        .getLiteralConclusions());
                currentConclusions.remove(resolvingLiteral);
                currentConclusions.remove(Util.invertLiteral(resolvingLiteral));
                currentNode = proof.addProofNode(
                        proof.freshNodeName("res.", ""), VeriTToken.RESOLUTION,
                        currentConclusions, subProofs, null, false);
            }

            return currentNode;
        }
    }

    /**
     * Creates a colorable proof for a congruence between the given terms, using
     * the given justification.
     * 
     * @param congruenceJustification
     * @param term1
     *            instance of a non-global function
     * @param term2
     *            instance of a non-global function
     * @param proof
     *            the proof to which nodes will be added
     * @return the proof node that asserts the congruence, based on colorable
     *         leaves.
     */
    private static VeritProofNode congruenceJustificationToColorableProof(
            List<TransitivityCongruenceChain> congruenceJustification,
            UninterpretedFunctionInstance term1,
            UninterpretedFunctionInstance term2, VeritProof proof) {

        assert (congruenceJustification != null);
        assert (term1.getFunction().equals(term2.getFunction()));

        // Construct proof nodes for each chain in the congruence
        // justification. Remember the implied literals (for later
        // resolution).
        int size = congruenceJustification.size();
        List<VeritProofNode> proofsForCongruence = new ArrayList<VeritProofNode>(
                size);
        List<Formula> impliedLiterals = new ArrayList<Formula>(size);
        for (TransitivityCongruenceChain chain : congruenceJustification) {
            Set<Integer> chainPartitions = chain.getPartitionsFromSymbols();
            chainPartitions.remove(-1);
            assert (chainPartitions.size() <= 1);

            VeritProofNode currentNode = chain.toColorableProofBaseCase();
            proofsForCongruence.add(currentNode);
            Formula impliedLiteral = Util.getImpliedLiteral(currentNode
                    .getLiteralConclusions());
            assert (Util.isGlobal(impliedLiteral));
            impliedLiterals.add(impliedLiteral);
        }

        // Create the the implied literal of the congruence
        List<DomainTerm> terms = new ArrayList<DomainTerm>(2);
        terms.add(term1);
        terms.add(term2);
        DomainEq congruenceImpliedLiteral = DomainEq.create(terms, true);

        List<Formula> congruenceConclusions = new ArrayList<Formula>(
                impliedLiterals.size() + 1);
        for (Formula literal : impliedLiterals) {
            NotFormula negatedLiteral = NotFormula.create(literal);
            congruenceConclusions.add(negatedLiteral);
        }
        congruenceConclusions.add(congruenceImpliedLiteral);
        VeritProofNode congruenceNode = proof.addProofNode(
                proof.freshNodeName("congr.", ""), VeriTToken.EQ_CONGRUENT,
                congruenceConclusions, null, null, false);

        VeritProofNode currentNode = congruenceNode;
        for (VeritProofNode currentProofForCongruence : proofsForCongruence) {
            List<VeritProofNode> subProofs = new ArrayList<VeritProofNode>(2);
            subProofs.add(currentProofForCongruence);
            subProofs.add(currentNode);
            String nodeName = proof.freshNodeName("res.", "");
            Formula resolvingLiteral = Util.findResolvingLiteral(subProofs);
            List<Formula> conclusions = new ArrayList<Formula>(subProofs.get(0)
                    .getLiteralConclusions().size()
                    + subProofs.get(1).getLiteralConclusions().size());
            conclusions.addAll(subProofs.get(0).getLiteralConclusions());
            conclusions.addAll(subProofs.get(1).getLiteralConclusions());
            conclusions.remove(resolvingLiteral);
            conclusions.remove(Util.invertLiteral(resolvingLiteral));
            currentNode = proof.addProofNode(nodeName, VeriTToken.RESOLUTION,
                    conclusions, subProofs, null, false);
        }
        return currentNode;
    }

    /**
     * Converts a chain with two global Ends into a colorable proof.
     * 
     * @return the colorable proof.
     */
    private VeritProofNode chainWithGlobalEndsToColorableProof() {

        assert (this.getStartPartition() == -1);
        assert (this.getEndPartition() == -1);

        Set<Integer> partitions = new HashSet<Integer>();
        TransitivityCongruenceChainElement newStart = null;
        TransitivityCongruenceChainElement current = start;
        while (current != null) {
            partitions.addAll(current.getTerm().getPartitionsFromSymbols());
            partitions.remove(-1);
            if (partitions.size() > 1) {
                partitions.removeAll(current.getTerm()
                        .getPartitionsFromSymbols());
                break;
            }
            current = current.getNext();
        }
        if (current == null)
            newStart = this.getEnd();
        else
            newStart = this.getPredecessor(current);
        assert (newStart != start);
        assert (newStart.getTermPartition() == -1);

        // Collect literals from the first part of the chain
        List<Formula> conclusions = new ArrayList<Formula>();
        current = start;
        while (current != newStart) {
            for (Formula literal : current.usedLiterals())
                conclusions.add(NotFormula.create(literal));
            current = current.getNext();
        }

        // Create and add the "shortcut"-literal, that connect from current to
        // the end. This one will be used for resolution.
        List<DomainTerm> terms = new ArrayList<DomainTerm>(2);
        terms.add(current.getTerm());
        terms.add(target);
        Formula resolvingLiteral = DomainEq.create(terms, true);
        conclusions.add(NotFormula.create(resolvingLiteral));

        // Add the implied literal of the first part of the chain
        List<DomainTerm> terms2 = new ArrayList<DomainTerm>(2);
        terms2.add(start.getTerm());
        terms2.add(target);
        conclusions.add((DomainEq.create(terms2, true)));

        // Remove negative reflexive literals (they are false anyway)
        Util.removeReflexiveLiterals(conclusions);

        VeritProofNode node1 = proof.addProofNode("tcc_left_"
                + TransitivityCongruenceChain.proofNodeCounter++,
                VeriTToken.TRANS_CONGR, conclusions, null, null, false);
        assert (node1.isColorable());

        if (newStart == this.getEnd()) {
            // base case for recursion; whole chain in one partition
            return node1;
        }

        TransitivityCongruenceChain secondPart = new TransitivityCongruenceChain(
                newStart, target, proof);
        assert (secondPart.getStartPartition() == -1);
        assert (secondPart.getEndPartition() == -1);
        VeritProofNode node2 = secondPart.chainWithGlobalEndsToColorableProof();

        List<VeritProofNode> clauses = new ArrayList<VeritProofNode>(2);
        clauses.add(node1);
        clauses.add(node2);
        List<Formula> finalConclusions = new ArrayList<Formula>();
        finalConclusions.addAll(node1.getLiteralConclusions());
        finalConclusions.addAll(node2.getLiteralConclusions());
        finalConclusions.remove(resolvingLiteral);
        finalConclusions.remove(Util.invertLiteral(resolvingLiteral));

        VeritProofNode resNode = proof.addProofNode("tcc_res_"
                + TransitivityCongruenceChain.proofNodeCounter++,
                VeriTToken.RESOLUTION, finalConclusions, clauses, null, false);

        return resNode;
    }

    /**
     * If a congruence link spans over more than one partition, a global
     * intermediate is added in between.
     */
    private void splitUncolorableCongruenceLinks() {
        TransitivityCongruenceChainElement current = this.start;
        while (current.hasNext()) {
            if (current.getCongruenceJustification() != null) {
                assert (current.getEqualityJustification() == null);
                Set<Integer> partitions = new HashSet<Integer>();
                // Reminder: Partitions of terms should not be added.
                // This causes a problem when the congruence is about a local
                // function.
                // Since there are no bad literals at this point, there are also
                // no bad terms. I.e., a local function is only applied to
                // correct local terms, or to global terms.
                // Thus, checking the partitions of the chain underlying
                // congruence chain should suffice.
                //
                // partitions.addAll(current.getTerm().getPartitionsFromSymbols());
                // partitions.addAll(current.getNext().getTerm()
                // .getPartitionsFromSymbols());
                for (TransitivityCongruenceChain chain : current
                        .getCongruenceJustification())
                    partitions.addAll(chain.getPartitionsFromSymbols());
                partitions.remove(-1);
                if (partitions.size() > 1)
                    this.splitUncolorableCongruenceLink(current);
            }
            current = current.getNext();
        }
    }

    /**
     * Splits the uncolorable congruence link at position <code>element</code>.
     * 
     * @param element
     *            the left side of an uncolorable congruence link in this chain
     */
    private void splitUncolorableCongruenceLink(
            TransitivityCongruenceChainElement element) {
        assert (element.hasNext());
        assert (element.getCongruenceJustification() != null);
        assert (element.getEqualityJustification() == null);

        List<List<TransitivityCongruenceChain>> listOfSegments = new ArrayList<List<TransitivityCongruenceChain>>();
        for (TransitivityCongruenceChain chain : element
                .getCongruenceJustification()) {
            chain.splitUncolorableCongruenceLinks();
            TransitivityCongruenceChain chainSegment = chain;
            List<TransitivityCongruenceChain> segments = new ArrayList<TransitivityCongruenceChain>();
            while (true) {
                segments.add(chainSegment);
                Set<Integer> partitions = new HashSet<Integer>();
                TransitivityCongruenceChainElement newStart = null;
                TransitivityCongruenceChainElement current = chainSegment.start;
                while (true) {
                    partitions.addAll(current.getTerm()
                            .getPartitionsFromSymbols());
                    partitions.remove(-1);
                    if (partitions.size() > 1) {
                        partitions.removeAll(current.getTerm()
                                .getPartitionsFromSymbols());
                        current = chainSegment.getPredecessor(current);
                        break;
                    }
                    if (!current.hasNext())
                        break;
                    current = current.getNext();
                }
                if (!current.hasNext()) { // whole chain is one segment.
                    break;
                } else {
                    newStart = current;
                    assert (newStart.getTermPartition() == -1);
                    assert (newStart != chainSegment.start);
                    chainSegment = chainSegment.split(newStart);
                }
            }
            listOfSegments.add(segments);
        }

        // Determine start and target partitions
        Set<Integer> partitions = element.getTerm().getPartitionsFromSymbols();
        partitions.remove(-1);
        assert (partitions.size() <= 1);
        int leftPartition = partitions.size() > 0 ? partitions.iterator()
                .next() : -1;
        partitions.clear();
        partitions = element.getNext().getTerm().getPartitionsFromSymbols();
        partitions.remove(-1);
        assert (partitions.size() <= 1);
        int rightPartition = partitions.size() > 0 ? partitions.iterator()
                .next() : -1;

        // Determine the function in question
        assert (element.getTerm() instanceof UninterpretedFunctionInstance);
        UninterpretedFunction function = ((UninterpretedFunctionInstance) element
                .getTerm()).getFunction();
        assert (element.getNext().getTerm() instanceof UninterpretedFunctionInstance);
        assert (((UninterpretedFunctionInstance) element.getNext().getTerm())
                .getFunction().equals(function));

        // Create the patch to splice in
        TransitivityCongruenceChain patch = new TransitivityCongruenceChain(
                element.getTerm(), element.getNext().getTerm(), this.proof);

        // Create intermediate elements from list of lists and attach them to
        // the patch

        // First step: From local partition to a global intermediate
        List<TransitivityCongruenceChain> firstJustification = new ArrayList<TransitivityCongruenceChain>();
        List<DomainTerm> firstIntermediateParameters = new ArrayList<DomainTerm>();
        for (List<TransitivityCongruenceChain> segments : listOfSegments) {
            assert (!segments.isEmpty());
            TransitivityCongruenceChain firstSegment = segments.get(0);
            partitions.clear();
            partitions = firstSegment.getPartitionsFromSymbols();
            partitions.remove(-1);
            assert (partitions.size() <= 1);
            assert (partitions.isEmpty() || partitions.contains(leftPartition) || Util
                    .isGlobal(firstSegment.getStart().getTerm()));
            if ((partitions.isEmpty() || partitions.contains(leftPartition))
                    && segments.size() > 1) {
                firstIntermediateParameters.add(firstSegment.getEndTerm());
                firstJustification.add(firstSegment);
                segments.remove(0);
            } else {
                firstIntermediateParameters.add(firstSegment.getStart()
                        .getTerm());
                firstJustification.add(new TransitivityCongruenceChain(
                        firstSegment.start.getTerm(), this.proof));
            }
        }
        UninterpretedFunctionInstance nextTerm = null;
        try {
            nextTerm = UninterpretedFunctionInstance.create(function,
                    firstIntermediateParameters);
        } catch (Exception exc) {
            throw new RuntimeException(
                    "Unexpected exception while creating UninterpretedFunctionInstance. This should not happen.",
                    exc);
        }
        boolean firstAttach = patch.getEnd().tryAttach(nextTerm,
                firstJustification);
        assert (firstAttach);

        // Loop: From one global intermediate to another global intermediate
        while (!(Util.allElementsSizeOne(listOfSegments))) {
            List<TransitivityCongruenceChain> currentJustification = new ArrayList<TransitivityCongruenceChain>();
            List<DomainTerm> currentIntermediateParameters = new ArrayList<DomainTerm>();
            Integer partitionOfThisStep = null;
            for (List<TransitivityCongruenceChain> segments : listOfSegments) {
                assert (!segments.isEmpty());
                TransitivityCongruenceChain currentSegment = segments.get(0);
                if (segments.size() == 1) {
                    currentJustification.add(new TransitivityCongruenceChain(
                            currentSegment.start.getTerm(), this.proof));
                    currentIntermediateParameters.add(currentSegment.start
                            .getTerm());
                } else {
                    partitions.clear();
                    partitions = currentSegment.getPartitionsFromSymbols();
                    partitions.remove(-1);
                    assert (partitions.size() <= 1);
                    if (!partitions.isEmpty()) {
                        if (partitionOfThisStep == null) {
                            partitionOfThisStep = partitions.iterator().next();
                            currentJustification.add(currentSegment);
                            currentIntermediateParameters.add(currentSegment
                                    .getEndTerm());
                            segments.remove(0);
                        } else {
                            if (partitions.iterator().next()
                                    .equals(partitionOfThisStep)) {
                                currentJustification.add(currentSegment);
                                currentIntermediateParameters
                                        .add(currentSegment.getEndTerm());
                                segments.remove(0);
                            } else {
                                currentJustification
                                        .add(new TransitivityCongruenceChain(
                                                currentSegment.start.getTerm(),
                                                this.proof));
                                currentIntermediateParameters
                                        .add(currentSegment.start.getTerm());
                            }
                        }
                    } else {
                        currentJustification.add(currentSegment);
                        currentIntermediateParameters.add(currentSegment
                                .getEndTerm());
                        segments.remove(0);
                    }
                }
            }
            try {
                nextTerm = UninterpretedFunctionInstance.create(function,
                        currentIntermediateParameters);
            } catch (Exception exc) {
                throw new RuntimeException(
                        "Unexpected exception while creating UninterpretedFunctionInstance. This should not happen.",
                        exc);
            }
            boolean currentAttach = patch.getEnd().tryAttach(nextTerm,
                    currentJustification);
            assert (currentAttach);
        }

        // Last step: From a global intermediate to a local partition
        assert (Util.allElementsSizeOne(listOfSegments));
        List<TransitivityCongruenceChain> lastJustification = new ArrayList<TransitivityCongruenceChain>();
        List<DomainTerm> lastIntermediateParameters = new ArrayList<DomainTerm>();
        for (List<TransitivityCongruenceChain> segments : listOfSegments) {
            assert (segments.size() == 1);
            TransitivityCongruenceChain currentSegment = segments.get(0);
            partitions.clear();
            partitions = currentSegment.getPartitionsFromSymbols();
            partitions.remove(-1);
            assert (partitions.size() <= 1);
            assert (partitions.isEmpty() || partitions.contains(rightPartition) || Util
                    .isGlobal(currentSegment.getEndTerm()));
            lastIntermediateParameters.add(currentSegment.getEndTerm());
            lastJustification.add(currentSegment);
            segments.remove(0);
        }
        try {
            nextTerm = UninterpretedFunctionInstance.create(function,
                    lastIntermediateParameters);
        } catch (Exception exc) {
            throw new RuntimeException(
                    "Unexpected exception while creating UninterpretedFunctionInstance. This should not happen.",
                    exc);
        }
        patch.getEnd().tryAttach(nextTerm, lastJustification);

        // Now splice in the patch
        this.splice(element, patch);
    }

    /**
     * Splits this chain at the given <code>element</code> and returns the
     * second part.
     * 
     * @param element
     * @return the second part of the split of <code>this</code> chain, split at
     *         the given <code>element</code>.
     */
    private TransitivityCongruenceChain split(
            TransitivityCongruenceChainElement element) {

        assert (element.hasNext());

        // TransitivityCongruenceChainElement current = this.start;
        // Set<Integer> partitions1 = new HashSet<Integer>();
        // while (current != element) {
        // partitions1.addAll(current.getTerm().getPartitionsFromSymbols());
        // current = current.getNext();
        // assert (current != null);
        // }

        TransitivityCongruenceChain result = new TransitivityCongruenceChain(
                new TransitivityCongruenceChainElement(element), target, proof);

        this.target = element.getTerm();
        element.makeNextNull();
        return result;
    }

    /**
     * 
     * @return a set of formulas used as links in this chain.
     */
    public Set<Formula> usedLiterals() {
        Set<Formula> result = new HashSet<Formula>();
        TransitivityCongruenceChainElement current = start;
        while (current.hasNext()) {
            result.addAll(current.usedLiterals());
            current = current.getNext();
        }
        return result;
    }

    /**
     * Splices the given <code>patch</code> into <code>this</code> chain,
     * starting at <code>start</code>.
     * 
     * @param start
     *            the element where to start the splice. Must have the same term
     *            as the first element of <code>patch</code>.
     * @param patch
     *            the (longer) chain to splice in
     */
    public void splice(TransitivityCongruenceChainElement start,
            TransitivityCongruenceChain patch) {
        assert (start != null);
        assert (patch != null);
        assert (start.hasNext());
        assert (start.getTerm().equals(patch.getStart().getTerm()));
        assert (start.getNext().getTerm().equals(patch.getEndTerm()));

        // Right splice must come first, otherwise we already overwrite
        // start.getNext()
        start.getNext().makeRightSplice(patch.getEnd());
        start.makeLeftSplice(patch.getStart());
    }

    /**
     * Traverses this chain and splits it at the first global term found. Both
     * halfs contain the global term at their originally joint side. If no
     * global term is found, uncolorable congruence links are split, before
     * attempting to find a global term again.
     * 
     * @return the second half of the chain.
     */
    public TransitivityCongruenceChain splitAtGlobalTerm() {

        TransitivityCongruenceChainElement currentElement = this.start;
        while (currentElement != null) {
            if (Util.isGlobal(currentElement.getTerm()))
                break;
            currentElement = currentElement.getNext();
        }

        if (currentElement == null) {
            this.splitUncolorableCongruenceLinks();
            currentElement = this.start;
            while (currentElement != null) {
                if (Util.isGlobal(currentElement.getTerm()))
                    break;
                currentElement = currentElement.getNext();
            }
        }

        assert (currentElement != null);
        assert (currentElement != this.start);

        TransitivityCongruenceChainElement copy = new TransitivityCongruenceChainElement(
                currentElement);
        currentElement.makeNextNull();

        DomainTerm oldTarget = this.target;
        this.target = currentElement.getTerm();
        assert (this.isComplete());

        TransitivityCongruenceChain result = new TransitivityCongruenceChain(
                copy, oldTarget, this.proof);
        assert (result.isComplete());
        return result;
    }

    /**
     * 
     * @return the set of partitions formed by all symbols in this chain.
     */
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> result = new HashSet<Integer>();
        TransitivityCongruenceChainElement current = this.start;
        while (current.hasNext()) {
            result.addAll(current.getPartitionsFromSymbols());
            current = current.getNext();
        }
        return result;
    }

    /**
     * 
     * @return <code>true</code> iff at most one partition appears in the used
     *         literals of this chain
     */
    public boolean isColorable() {
        Set<Integer> partitions = new TreeSet<Integer>();
        for (Formula literal : this.usedLiterals())
            partitions.addAll(literal.getPartitionsFromSymbols());
        partitions.remove(-1);
        return partitions.size() <= 1;
    }

    /**
     * 
     * @return the term (currently) at the end of this chain.
     */
    public DomainTerm getEndTerm() {
        TransitivityCongruenceChainElement current = start;
        assert (current != null);
        while (current.getNext() != null)
            current = current.getNext();
        assert (current != null);
        return current.getTerm();
    }

    /**
     * 
     * @return the element (currently) at the end of this chain.
     */
    public TransitivityCongruenceChainElement getEnd() {
        TransitivityCongruenceChainElement current = start;
        assert (current != null);
        while (current.getNext() != null)
            current = current.getNext();
        assert (current != null);
        return current;
    }

    /**
     * 
     * @return <code>true</code> if this chain has reached its target.
     */
    public boolean isComplete() {
        assert (target != null);
        return target.equals(getEndTerm());
    }

    /**
     * 
     * @return the length (number of elements) of this chain (counting complex
     *         congruence edges as 1).
     */
    public int length() {
        int count = 1;
        TransitivityCongruenceChainElement current = start;
        while (current.getNext() != null) {
            current = current.getNext();
            count++;
        }
        assert (current.getNext() == null);
        return count;
    }

    /**
     * @return the <code>start</code>
     */
    public TransitivityCongruenceChainElement getStart() {
        return start;
    }

    /**
     * @return the <code>target</code>
     */
    public DomainTerm getTarget() {
        return target;
    }

    /**
     * 
     * @return the partition of the start term.
     */
    public int getStartPartition() {
        Set<Integer> partitions = start.getTerm().getPartitionsFromSymbols();
        if (partitions.size() > 1)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        return partitions.iterator().next();
    }

    /**
     * 
     * @return the partition of the end term.
     */
    public int getEndPartition() {
        Set<Integer> partitions = this.getEndTerm().getPartitionsFromSymbols();
        if (partitions.size() > 1)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        return partitions.iterator().next();
    }

    /**
     * @return the reversed chain
     */
    public TransitivityCongruenceChain reverse() {
        List<Justification> reverseJustifications = new ArrayList<Justification>();
        TransitivityCongruenceChainElement currentElement = this.start;
        while (currentElement != null) {
            Justification justification = currentElement.getJustficiation();
            if (justification != null)
                reverseJustifications.add(0, justification.reverse());
            currentElement = currentElement.getNext();
        }
        TransitivityCongruenceChain result = new TransitivityCongruenceChain(
                this.getEndTerm(), this.start.getTerm(), reverseJustifications,
                this.proof);
        return result;
    }

    /**
     * 
     * @param element
     * @return the predecessor of <code>element</code> in this chain, or
     *         <code>null</code> if either <code>element</code> is not part of
     *         the chain, or is the first element.
     */
    public TransitivityCongruenceChainElement getPredecessor(
            TransitivityCongruenceChainElement element) {
        assert (element != this.start);
        TransitivityCongruenceChainElement currentElement = this.start;
        while (currentElement.hasNext()) {
            if (currentElement.getNext().equals(element))
                return currentElement;
            currentElement = currentElement.getNext();
        }
        return null;
    }

}
