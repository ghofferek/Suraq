/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util.chain;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.proof.VeritProofNode;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.util.Util;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TransitivityCongruenceChain {

    /**
     * The starting point of the chain.
     */
    private final TransitivityCongruenceChainElement start;

    /**
     * The target of the chain.
     */
    private final DomainTerm target;

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
                equalities);
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
            List<DomainEq> implyingLiterals) {
        assert (impliedLiteral != null);
        assert (implyingLiterals != null);
        assert (!implyingLiterals.isEmpty());
        assert (Util.isLiteral(impliedLiteral));
        assert (!Util.isNegativeLiteral(impliedLiteral));

        // Make a copy of the list, as it will be modified along the way
        List<DomainEq> otherLiterals = new ArrayList<DomainEq>(implyingLiterals);

        TransitivityCongruenceChain chain = new TransitivityCongruenceChain(
                (DomainTerm) impliedLiteral.getTerms().get(0),
                (DomainTerm) impliedLiteral.getTerms().get(1));

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
                    chain.getEnd().tryAttach(otherInstance, justification);
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
                    .create(equality, literals);
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
     * @param target
     */
    private TransitivityCongruenceChain(DomainTerm start, DomainTerm target) {
        assert (start != null);
        assert (target != null);
        this.start = new TransitivityCongruenceChainElement(start);
        this.target = target;
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
    protected TransitivityCongruenceChainElement getEnd() {
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
