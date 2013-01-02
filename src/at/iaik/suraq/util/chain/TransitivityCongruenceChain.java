/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util.chain;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.proof.VeriTToken;
import at.iaik.suraq.proof.VeritProof;
import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.util.ImmutableArrayList;
import at.iaik.suraq.util.ImmutableSet;
import at.iaik.suraq.util.Util;

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
     * The conclusion of the proof node for which this was constructed. Needed
     * to know if additional literals must be added.
     */
    private ImmutableArrayList<Formula> targetLiterals;

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

        // Assuming the implied literal is the last one.
        Formula impliedLiteral = node.getLiteralConclusions().get(
                node.getLiteralConclusions().size() - 1);
        assert (Util.isLiteral(impliedLiteral));
        assert (!Util.isNegativeLiteral(impliedLiteral));
        assert (impliedLiteral instanceof DomainEq);
        assert (((DomainEq) impliedLiteral).isEqual());
        assert (((DomainEq) impliedLiteral).getTerms().size() == 2);
        assert (((DomainEq) impliedLiteral).getTerms().get(0) instanceof DomainTerm);
        assert (((DomainEq) impliedLiteral).getTerms().get(1) instanceof DomainTerm);

        List<DomainEq> equalities = new ArrayList<DomainEq>();
        for (Formula literal : node.getLiteralConclusions().subList(0,
                node.getLiteralConclusions().size() - 1)) {
            assert (Util.isNegativeLiteral(literal));
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

        // Make a copy of the list, as it will be modified along the way
        List<DomainEq> otherLiterals = new ArrayList<DomainEq>(implyingLiterals);

        TransitivityCongruenceChain chain = new TransitivityCongruenceChain(
                (DomainTerm) impliedLiteral.getTerms().get(0),
                (DomainTerm) impliedLiteral.getTerms().get(1), node);

        while (!otherLiterals.isEmpty() && !chain.isComplete()) {
            // Try attaching equalities, as long as possible
            int oldLength = -1;
            int newLength = -1;
            do {
                oldLength = chain.length();
                for (DomainEq equality : otherLiterals) {
                    if (chain.getEnd().tryAttach(equality)) {
                        otherLiterals.remove(equality);
                        assert (chain.length() == oldLength + 1);
                        break;
                    }
                }
                newLength = chain.length();
                assert (oldLength > 0);
                assert (newLength > 0);
            } while (newLength > oldLength);

            if (chain.isComplete() || otherLiterals.isEmpty())
                break;

            // Now try adding a congruence equality
            assert (chain.getEndTerm() instanceof UninterpretedFunctionInstance);
            Set<UninterpretedFunctionInstance> otherInstances = TransitivityCongruenceChain
                    .getOtherFunctionInstances(
                            (UninterpretedFunctionInstance) chain.getEndTerm(),
                            otherLiterals);
            for (UninterpretedFunctionInstance otherInstance : otherInstances) {
                List<TransitivityCongruenceChain> justification = TransitivityCongruenceChain
                        .constructJustification(
                                (UninterpretedFunctionInstance) chain
                                        .getEndTerm(), otherInstance,
                                otherLiterals);
                if (justification != null) {
                    boolean tmp = chain.getEnd().tryAttach(otherInstance,
                            justification);
                    assert (tmp);
                    break;
                }
            }
        }

        return chain;
    }

    /**
     * 
     * @param instance1
     * @param instance2
     * @param literals
     * @return a list of justifications for an equality between
     *         <code>instance1</code> and <code>instance2</code>, or
     *         <code>null</code> if none can be constructed.
     */
    private static List<TransitivityCongruenceChain> constructJustification(
            UninterpretedFunctionInstance instance1,
            UninterpretedFunctionInstance instance2, List<DomainEq> literals) {

        assert (instance1.getFunction().equals(instance2.getFunction()));
        assert (instance1.getParameters().size() == instance2.getParameters()
                .size());
        List<TransitivityCongruenceChain> result = new ArrayList<TransitivityCongruenceChain>(
                instance1.getParameters().size());

        for (int count = 0; count < instance1.getParameters().size(); count++) {
            List<DomainTerm> paramPair = new ArrayList<DomainTerm>(2);
            paramPair.add(instance1.getParameters().get(count));
            paramPair.add(instance2.getParameters().get(count));
            DomainEq equality = DomainEq.create(paramPair, true);
            TransitivityCongruenceChain chain = TransitivityCongruenceChain
                    .create(equality, literals, null);
            if (!chain.isComplete())
                return null;
            result.add(chain);
        }
        return result;
    }

    /**
     * @param instance
     * @param literals
     * @return a <code>Set</code> of other instances of the same uninterpreted
     *         function as <code>instance</code> contained in
     *         <code>literals</code>.
     */
    private static Set<UninterpretedFunctionInstance> getOtherFunctionInstances(
            UninterpretedFunctionInstance instance, List<DomainEq> literals) {
        Set<UninterpretedFunctionInstance> result = new HashSet<UninterpretedFunctionInstance>();
        for (DomainEq literal : literals) {
            for (Term term : literal.getTerms()) {
                if (term.equals(instance))
                    continue;
                if (term instanceof UninterpretedFunctionInstance) {
                    if (((UninterpretedFunctionInstance) term).getFunction()
                            .equals(instance.getFunction())) {
                        result.add((UninterpretedFunctionInstance) term);
                    }
                }
            }
        }
        return result;
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
            this.targetLiterals = node.getLiteralConclusions();
        } else {
            this.proof = null;
            this.targetLiterals = null;
        }
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
     * @param targetLiterals
     */
    private TransitivityCongruenceChain(
            TransitivityCongruenceChainElement start, DomainTerm target,
            VeritProof proof, List<Formula> targetLiterals) {
        this.start = start;
        this.proof = proof;
        this.targetLiterals = new ImmutableArrayList<Formula>(targetLiterals);
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
        List<Formula> literals = new ArrayList<Formula>();
        literals.add(this.start.getEqualityJustification());
        this.targetLiterals = new ImmutableArrayList<Formula>(literals);

        assert (this.isComplete());
    }

    /**
     * 
     * @return a proof node that proofs the targetLiterals, and is split in
     *         colorable subproofs.
     */
    public VeritProofNode toColorableProof() {
        assert (targetLiterals != null);
        assert (proof != null);

        splitUncolorableCongruenceLinks();

        Set<Integer> partitions = new HashSet<Integer>();
        TransitivityCongruenceChainElement newStart = null;
        TransitivityCongruenceChainElement current = start;
        while (true) {
            partitions.addAll(current.getTerm().getPartitionsFromSymbols());
            partitions.remove(-1);
            if (!current.hasNext() || partitions.size() > 1) {
                partitions.removeAll(current.getTerm()
                        .getPartitionsFromSymbols());
                break;
            }
            current = current.getNext();
        }
        newStart = current;
        assert (newStart != start);

        // Collect literals from the first part of the chain
        List<Formula> conclusions = new ArrayList<Formula>();
        current = start;
        while (current != newStart) {
            conclusions.addAll(current.usedLiterals());
            current = current.getNext();
        }

        // Create and add the "shortcut"-literal, that connect from current to
        // the end. This one will be used for resolution.
        List<DomainTerm> terms = new ArrayList<DomainTerm>(2);
        terms.add(current.getTerm());
        terms.add(target);
        Formula resolvingLiteral = DomainEq.create(terms, true);
        conclusions.add(NotFormula.create(resolvingLiteral));

        // Add unused literals of the correct partition
        for (Formula unusedLiteral : this.unusedLiterals()) {
            Set<Integer> literalPartitions = unusedLiteral
                    .getPartitionsFromSymbols();
            literalPartitions.remove(-1);
            assert (literalPartitions.size() <= 1);
            if (partitions.containsAll(literalPartitions))
                conclusions.add(unusedLiteral);
        }

        // Add the implied literal of the first part of the chain
        List<DomainTerm> terms2 = new ArrayList<DomainTerm>(2);
        terms2.add(start.getTerm());
        terms2.add(target);
        conclusions.add((DomainEq.create(terms2, true)));

        VeritProofNode node1 = proof.addProofSet("tcc_n1_"
                + TransitivityCongruenceChain.proofNodeCounter++,
                VeriTToken.EQ_TRANSITIVE, conclusions, null, null);

        if (newStart == this.getEnd()) {
            // base case for recursion; whole chain in one partition
            assert (node1.getLiteralConclusionsAsSet().equals(ImmutableSet
                    .create(targetLiterals)));
            return node1;
        }

        List<Formula> newTargetLiterals = targetLiterals
                .removeAllFromCopy(conclusions);

        TransitivityCongruenceChain secondPart = new TransitivityCongruenceChain(
                newStart, target, proof, newTargetLiterals);
        VeritProofNode node2 = secondPart.toColorableProof();

        List<VeritProofNode> clauses = new ArrayList<VeritProofNode>(2);
        clauses.add(node1);
        clauses.add(node2);
        List<Formula> finalConclusions = new ArrayList<Formula>();
        finalConclusions.addAll(node1.getLiteralConclusions());
        finalConclusions.addAll(node2.getLiteralConclusions());
        finalConclusions.remove(resolvingLiteral);
        finalConclusions.remove(Util.invertLiteral(resolvingLiteral));

        VeritProofNode resNode = proof.addProofSet("tcc_res_"
                + TransitivityCongruenceChain.proofNodeCounter++,
                VeriTToken.RESOLUTION, conclusions, clauses, null);

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
                partitions.addAll(current.getTerm().getPartitionsFromSymbols());
                partitions.addAll(current.getNext().getTerm()
                        .getPartitionsFromSymbols());
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
                    if (!current.hasNext() || partitions.size() > 1) {
                        partitions.removeAll(current.getTerm()
                                .getPartitionsFromSymbols());
                        break;
                    }
                    current = current.getNext();
                }
                newStart = current;
                assert (newStart != chainSegment.start);
                if (!newStart.hasNext()) { // whole chain is one segment.
                    break;
                } else {
                    chainSegment = chainSegment.split(newStart);
                }
            }
            listOfSegments.add(segments);
        }

        // Determine start and target partitions
        Set<Integer> partitions = element.getTerm().getPartitionsFromSymbols();
        partitions.remove(-1);
        assert (partitions.size() == 1);
        int leftPartition = partitions.iterator().next();
        partitions.clear();
        partitions = element.getNext().getTerm().getPartitionsFromSymbols();
        partitions.remove(-1);
        assert (partitions.size() == 1);
        int rightPartition = partitions.iterator().next();

        // Determine the function in question
        assert (element.getTerm() instanceof UninterpretedFunctionInstance);
        UninterpretedFunction function = ((UninterpretedFunctionInstance) element
                .getTerm()).getFunction();
        assert (element.getNext().getTerm() instanceof UninterpretedFunctionInstance);
        assert (((UninterpretedFunctionInstance) element.getNext().getTerm())
                .getFunction().equals(function));

        // Create the patch to splice in
        TransitivityCongruenceChain patch = new TransitivityCongruenceChain(
                element.getTerm(), element.getNext().getTerm(), null);

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
            if ((partitions.isEmpty() || partitions.contains(leftPartition))
                    && segments.size() > 1) {
                firstIntermediateParameters.add(firstSegment.getEndTerm());
                firstJustification.add(firstSegment);
                segments.remove(0);
            } else {
                firstIntermediateParameters.add(firstSegment.getStart()
                        .getTerm());
                firstJustification.add(new TransitivityCongruenceChain(
                        firstSegment.start.getTerm(), null));
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
                            currentIntermediateParameters.add(currentSegment
                                    .getEndTerm());
                            segments.remove(0);
                        } else {
                            currentJustification
                                    .add(new TransitivityCongruenceChain(
                                            currentSegment.start.getTerm(),
                                            null));
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
            assert (partitions.isEmpty() || partitions.contains(rightPartition));
            lastIntermediateParameters.add(currentSegment.getEndTerm());
            lastJustification.add(currentSegment);
            segments.remove(0);
        }
        try {
            nextTerm = UninterpretedFunctionInstance.create(function,
                    firstIntermediateParameters);
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

        List<Formula> targetLiterals1 = new ArrayList<Formula>();
        List<Formula> targetLiterals2 = new ArrayList<Formula>();
        TransitivityCongruenceChainElement current = this.start;
        Set<Integer> partitions1 = new HashSet<Integer>();
        while (current != element) {
            partitions1.addAll(current.getTerm().getPartitionsFromSymbols());
            targetLiterals1.addAll(current.usedLiterals());
            current = current.getNext();
            assert (current != null);
        }
        TransitivityCongruenceChainElement current2 = current;
        while (current2.hasNext()) {
            targetLiterals2.addAll(current2.usedLiterals());
        }
        List<Formula> unusedLiterals = targetLiterals.editableCopy();
        unusedLiterals.removeAll(targetLiterals1);
        unusedLiterals.removeAll(targetLiterals2);
        for (Formula literal : unusedLiterals) {
            if (partitions1.containsAll(literal.getPartitionsFromSymbols()))
                targetLiterals1.add(literal);
            else
                targetLiterals2.add(literal);
        }

        TransitivityCongruenceChain result = new TransitivityCongruenceChain(
                new TransitivityCongruenceChainElement(element), target, proof,
                targetLiterals2);

        this.targetLiterals = new ImmutableArrayList<Formula>(targetLiterals1);
        this.target = element.getTerm();
        element.makeNextNull();
        return result;
    }

    /**
     * 
     * @return a set of formulas used as links in this chain.
     */
    protected Set<Formula> usedLiterals() {
        Set<Formula> result = new HashSet<Formula>();
        TransitivityCongruenceChainElement current = start;
        while (current.hasNext()) {
            result.addAll(current.usedLiterals());
        }
        return result;
    }

    /**
     * 
     * @return a set of literals that occur in the target literals, but are not
     *         used (or empty, if there are not <code>targetLiterals</code>.
     */
    private Set<Formula> unusedLiterals() {
        if (targetLiterals == null)
            return new HashSet<Formula>();
        Set<Formula> result = new HashSet<Formula>(targetLiterals);
        result.removeAll(this.usedLiterals());
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
        start.makeLeftSplice(patch.getStart());
        patch.getEnd().makeRightSplice(start.getNext());
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

}
