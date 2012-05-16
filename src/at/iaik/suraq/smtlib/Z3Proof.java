/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
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
import at.iaik.suraq.smtlib.formula.FunctionMacro;
import at.iaik.suraq.smtlib.formula.NotFormula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalEq;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtsolver.SMTSolver;
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
        this.assertPartition = -1;
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
        this.setAssertPartition();
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
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = consequent.getPartitionsFromSymbols();

        for (Z3Proof proof : subProofs)
            partitions.addAll(proof.getPartitionsFromSymbols());

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
    public Set<Integer> getPartitionsFromAsserts() {

        Set<Integer> assertPartitions = new HashSet<Integer>();
        for (Z3Proof z3Proofchild : this.subProofs) {
            assertPartitions.addAll(z3Proofchild.getPartitionsFromAsserts());
        }

        if (proofType.equals(SExpressionConstants.ASSERTED)) {
            if (assertPartition <= 0)
                assert (false);
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
            Set<Integer> partitionsFromAsserts = subProofs.get(0)
                    .getPartitionsFromAsserts();
            assert (!partitionsFromAsserts.contains(new Integer(-1)));
            if (partitionsFromAsserts.size() > 1) {
                subProofs.get(0).localLemmasToAssertions();
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
            for (Z3Proof child : subProofs)
                child.localLemmasToAssertions();
    }

    public void removeLocalSubProofs() {
        Set<Integer> partitionsFromAsserts = this.getPartitionsFromAsserts();

        if (partitionsFromAsserts.size() == 1) {
            assert (!partitionsFromAsserts.contains((new Integer(-1))));
            Set<Integer> symbolPartitions = this.getPartitionsFromSymbols();
            assert (symbolPartitions.size() > 0);
            symbolPartitions.remove(-1);
            if (symbolPartitions.equals(partitionsFromAsserts)
                    || symbolPartitions.size() == 0) {
                proofType = SExpressionConstants.ASSERTED;
                this.setAssertPartition();
                subProofs = new ArrayList<Z3Proof>();
                return;
            }
        }

        for (Z3Proof child : subProofs) {
            child.removeLocalSubProofs();
        }
    }

    public void dealWithModusPonens() {

        if (this.proofType.equals(SExpressionConstants.MODUS_PONENS)) {
            assert (subProofs.size() == 2);
            assert (this.hasSingleLiteralConsequent());
            Formula consequentLiteral = Util.getSingleLiteral(consequent);
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
                    child3 = child2.subProofs.get(1);
                    child2 = child2.subProofs.get(0);
                    assert (child2.hasSingleLiteralConsequent());
                    assert (child3.hasSingleLiteralConsequent());
                    break;
                }
            }
            assert (child2 != null);
            assert (child3 != null);
            Formula literal2 = Util.getSingleLiteral(child2.consequent);
            Formula literal3 = Util.getSingleLiteral(child3.consequent);

            assert (consequentLiteral instanceof DomainEq);
            assert (literal1 instanceof DomainEq);
            assert (literal2 instanceof DomainEq);
            assert (literal3 instanceof DomainEq);

            EqualityFormula eq1 = (DomainEq) literal1;
            EqualityFormula eq2 = (DomainEq) literal2;
            EqualityFormula eq3 = (DomainEq) literal3;
            EqualityFormula consequentEq = (DomainEq) consequentLiteral;

            List<Z3Proof> proofList = new ArrayList<Z3Proof>();

            if (consequentEq.getTerms().get(0).equals(eq1.getTerms().get(0))) {
                if (eq1.getTerms().get(1).equals(eq2.getTerms().get(0))) {
                    proofList.add(child1);
                    proofList.add(child2);
                    assert (eq2.getTerms().get(1).equals(eq3.getTerms().get(0)));
                    proofList.add(child3);
                } else {
                    assert (eq1.getTerms().get(1).equals(eq3.getTerms().get(0)));
                    proofList.add(child1);
                    proofList.add(child3);
                    assert (eq3.getTerms().get(1).equals(eq2.getTerms().get(0)));
                    proofList.add(child2);
                }
            } else if (consequentEq.getTerms().get(0)
                    .equals(eq2.getTerms().get(0))) {
                if (eq2.getTerms().get(1).equals(eq1.getTerms().get(0))) {
                    proofList.add(child2);
                    proofList.add(child1);
                    if (eq1.getTerms().get(1).equals(eq3.getTerms().get(0)))
                        proofList.add(child3);
                    else {
                        // sometimes this term occurs "reverse" in the proof.
                        // Quick Hack: Check second direction.
                        assert ((eq1.getTerms().get(1).equals(eq3.getTerms()
                                .get(1))));
                        proofList.add(Z3Proof.createSymmetryProof(child3));
                    }
                } else {
                    assert (eq2.getTerms().get(1).equals(eq3.getTerms().get(0)));
                    proofList.add(child2);
                    proofList.add(child3);
                    assert (eq3.getTerms().get(1).equals(eq1.getTerms().get(0)));
                    proofList.add(child1);
                }
            } else {
                assert (consequentEq.getTerms().get(0).equals(eq3.getTerms()
                        .get(0)));
                if (eq3.getTerms().get(1).equals(eq1.getTerms().get(0))) {
                    proofList.add(child3);
                    proofList.add(child1);
                    assert (eq1.getTerms().get(1).equals(eq2.getTerms().get(0)));
                    proofList.add(child2);
                } else {
                    assert (eq3.getTerms().get(1).equals(eq2.getTerms().get(0)));
                    proofList.add(child3);
                    proofList.add(child2);
                    assert (eq2.getTerms().get(1).equals(eq1.getTerms().get(0)));
                    proofList.add(child1);
                }
            }

            Z3Proof transProof = Z3Proof.createTransitivityProof(proofList);
            this.subProofs = transProof.subProofs;
            this.proofType = transProof.proofType;
            assert (this.consequent.transformToConsequentsForm()
                    .equals(transProof.consequent.transformToConsequentsForm()));
            this.consequent = transProof.consequent;

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
        assert (subProofs.size() == 2 || subProofs.size() == 3);
        assert (Util.makeLiteralPositive((subProofs.get(0).consequent
                .transformToConsequentsForm())) instanceof EqualityFormula);
        assert (Util.makeLiteralPositive(subProofs.get(1).consequent
                .transformToConsequentsForm()) instanceof EqualityFormula);
        assert (subProofs.size() == 3 ? Util.makeLiteralPositive(subProofs
                .get(2).consequent.transformToConsequentsForm()) instanceof EqualityFormula
                : true);

        EqualityFormula firstFormula = (EqualityFormula) Util
                .makeLiteralPositive(subProofs.get(0).consequent
                        .transformToConsequentsForm());
        EqualityFormula lastFormula = (EqualityFormula) Util
                .makeLiteralPositive(subProofs.get(subProofs.size() - 1).consequent
                        .transformToConsequentsForm());

        int numDisequalities = 0;
        for (Z3Proof child : subProofs) {
            if (Util.isNegativeLiteral(child.consequent
                    .transformToConsequentsForm()))
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

        Z3Proof result = new Z3Proof(SExpressionConstants.TRANSITIVITY,
                subProofs, newFormula);
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
        Formula literal = Util.makeLiteralPositive((premise.consequent
                .transformToConsequentsForm()));
        assert (literal instanceof EqualityFormula);
        boolean equal = Util.isAtom(premise.consequent
                .transformToConsequentsForm());

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
     * Checks recursive if node is valid. Therefore, whether the given Subproofs
     * together produces the consequent of the node. Also checks this property
     * recursive for every node of the subtree.
     * 
     * @return return true iv node is valid
     */
    public boolean checkZ3ProofNode() {

        SMTSolver z3 = SMTSolver.create(SMTSolver.z3_type, "lib/z3/bin/z3");

        if (this.subProofs.size() > 0) {

            List<Formula> conjuncts = new ArrayList<Formula>();
            for (Z3Proof subProof : this.subProofs) {
                conjuncts.add(subProof.consequent);
            }
            conjuncts.add(new NotFormula(this.consequent));
            Formula formulaToCheck = new AndFormula(conjuncts);

            String declarationStr = makeDeclarationsAndDefinitions(formulaToCheck);
            String formulaSmtStr = buildSMTDescription(declarationStr,
                    formulaToCheck.toString());

            z3.solve(formulaSmtStr);

            switch (z3.getState()) {
            case SMTSolver.UNSAT:
                break;
            case SMTSolver.SAT:
                throw new RuntimeException(
                        "Error while testing vality of Z3-node with Z3-solver: \n"
                                + "z3 tells us SAT, node is NOT valid.");
            default:
                System.out
                        .println("....Z3 OUTCOME ---->  UNKNOWN! CHECK ERROR STREAM.");
                throw (new RuntimeException(
                        "Z3 tells us UNKOWN STATE. CHECK ERROR STREAM."));
            }

            for (Z3Proof subProof : this.subProofs)
                subProof.checkZ3ProofNode();

        }
        return true;
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
}
