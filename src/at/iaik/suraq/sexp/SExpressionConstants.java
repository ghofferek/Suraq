/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.sexp;

/**
 * 
 * This class bundles some important SExpression constants.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SExpressionConstants {

    public static final SExpression ARRAY_TYPE = SExpression
            .fromString("(Array Value Value)");

    public static final Token VALUE_TYPE = (Token) SExpression
            .fromString("Value");

    public static final Token CONTROL_TYPE = (Token) SExpression
            .fromString("Control");

    public static final Token BOOL_TYPE = (Token) SExpression
            .fromString("Bool");

    public static final Token DECLARE_FUN = (Token) SExpression
            .fromString("declare-fun");

    public static final Token DEFINE_FUN = (Token) SExpression
            .fromString("define-fun");

    public static final Token ASSERT = (Token) SExpression.fromString("assert");

    public static final Token ASSERT_PARTITION = (Token) SExpression
            .fromString("assert-partition");

    public static final SExpression SET_LOGIC_SURAQ = SExpression
            .fromString("(set-logic Suraq)");

    public static final SExpression SET_LOGIC_QF_UF = SExpression
            .fromString("(set-logic QF_UF)");

    public static final SExpression SET_OPTION_PRODUCE_INTERPOLANT = SExpression
            .fromString("(set-option :produce-interpolants true)");

    public static final SExpression SET_OPTION_PROPAGATE_BOOLEANS_FALSE = SExpression
            .fromString("(set-option :propagate-booleans false)");

    public static final SExpression SET_OPTION_PROPAGATE_VALUES_FALSE = SExpression
            .fromString("(set-option :propagate-values false)");

    public static final SExpression DECLARE_SORT_VALUE = SExpression
            .fromString("(declare-sort " + SExpressionConstants.VALUE_TYPE
                    + " 0)");

    public static final SExpression CHECK_SAT = SExpression
            .fromString("(check-sat)");

    public static final Token TRUE = (Token) SExpression.fromString("true");

    public static final Token FALSE = (Token) SExpression.fromString("false");

    public static final Token AND = (Token) SExpression.fromString("and");

    public static final Token OR = (Token) SExpression.fromString("or");

    public static final Token XOR = (Token) SExpression.fromString("xor");

    public static final Token NOT = (Token) SExpression.fromString("not");

    public static final Token DISTINCT = (Token) SExpression
            .fromString("distinct");

    public static final Token EQUAL = (Token) SExpression.fromString("=");

    public static final Token ITE = (Token) SExpression.fromString("ite");

    public static final Token IMPLIES = (Token) SExpression.fromString("=>");

    public static final Token IMPLIES_ALT = (Token) SExpression
            .fromString("implies");

    public static final Token FORALL = (Token) SExpression.fromString("forall");

    public static final Token SELECT = (Token) SExpression.fromString("select");

    public static final Token STORE = (Token) SExpression.fromString("store");

    public static final Token NO_DEPENDENCE = (Token) SExpression
            .fromString(":no_dependence");

    public static final SExpression EMPTY = SExpression.fromString("()");

    public static final SExpression EXIT = SExpression.fromString("(exit)");

    public static final SExpression GET_PROOF = SExpression
            .fromString("(get-proof)");

    public static final SExpression AUTO_CONFIG_FALSE = SExpression
            .fromString("(set-option :auto-config false)");

    public static final SExpression PROOF_MODE_2 = SExpression
            .fromString("(set-option :PROOF_MODE  2)");

    public static final SExpression UNSAT = SExpression.fromString("unsat");

    public static final SExpression LET = SExpression.fromString("let");

    public static final SExpression UNDEF = SExpression.fromString("undef");
    public static final SExpression ASSERTED = SExpression
            .fromString("asserted");
    public static final SExpression GOAL = SExpression.fromString("goal");
    public static final SExpression MODUS_PONENS = SExpression
            .fromString("modus-ponens");
    public static final SExpression REFLEXIVITY = SExpression
            .fromString("reflexivity");
    public static final SExpression SYMMETRY = SExpression.fromString("symm");
    public static final SExpression TRANSITIVITY = SExpression
            .fromString("trans");
    public static final SExpression TRANSITIVITY_STAR = SExpression
            .fromString("transitivity-star");
    public static final SExpression MONOTONICITY = SExpression
            .fromString("monotonicity");
    public static final SExpression QUANT_INTRO = SExpression
            .fromString("quant-intro");
    public static final SExpression DISTRIBUTIVITY = SExpression
            .fromString("distributivity");
    public static final SExpression AND_ELIM = SExpression
            .fromString("and-elim");
    public static final SExpression NOT_OR_ELIM = SExpression
            .fromString("not-or-elim");
    public static final SExpression REWRITE = SExpression.fromString("rewrite");
    public static final SExpression REWRITE_STAR = SExpression
            .fromString("rewrite-star");
    public static final SExpression PULL_QUANT = SExpression
            .fromString("pull-quant");
    public static final SExpression PULL_QUANT_STAR = SExpression
            .fromString("pull-quant-star");
    public static final SExpression PUSH_QUANT = SExpression
            .fromString("push-quant");
    public static final SExpression ELIM_UNUSED_VARS = SExpression
            .fromString("elim-unused-vars");
    public static final SExpression DER = SExpression.fromString("der");
    public static final SExpression QUANT_INST = SExpression
            .fromString("quant-inst");
    public static final SExpression HYPOTHESIS = SExpression
            .fromString("hypothesis");
    public static final SExpression LEMMA = SExpression.fromString("lemma");
    public static final SExpression UNIT_RESOLUTION = SExpression
            .fromString("unit-resolution");
    public static final SExpression IFF_TRUE = SExpression
            .fromString("iff-true");
    public static final SExpression IFF_FALSE = SExpression
            .fromString("iff-false");
    public static final SExpression COMMUTATIVITY = SExpression
            .fromString("commutativity");
    public static final SExpression AXIOM = SExpression
            .fromString("def-axiom");
    public static final SExpression INTRO = SExpression.fromString("intro");
    public static final SExpression APPLY_DEF = SExpression
            .fromString("apply-def");
    public static final SExpression IFF_OEQ = SExpression.fromString("iff-oeq");
    public static final SExpression NNF_POS = SExpression.fromString("nnf-pos");
    public static final SExpression NNF_NEG = SExpression.fromString("nnf-neg");
    public static final SExpression NNF_STAR = SExpression
            .fromString("nnf-star");
    public static final SExpression CNF_STAR = SExpression
            .fromString("cnf-star");
    public static final SExpression SKOLEMIZE = SExpression
            .fromString("skolemize");
    public static final SExpression MODUS_PONENS_OEQ = SExpression
            .fromString("modus-pones-oeq");
    public static final SExpression TH_LEMMA = SExpression
            .fromString("th-lemma");
    public static final SExpression TRANS = SExpression.fromString("trans");
    public static final SExpression MP = SExpression.fromString("mp");
    public static final SExpression[] PROOF_TYPES = SExpressionConstants
            .createProofTypes();

    /**
     * Creates the definition of proof types
     * 
     * @return an <code>SExpression[]</code> declaring the proof types.
     */

    public static SExpression[] createProofTypes() {

        SExpression[] proofTypes = new SExpression[41];

        // see: z3_api.h
        proofTypes[0] = SExpressionConstants.UNDEF;
        proofTypes[1] = SExpressionConstants.TRUE;
        proofTypes[2] = SExpressionConstants.ASSERTED;
        proofTypes[3] = SExpressionConstants.GOAL;
        proofTypes[4] = SExpressionConstants.MODUS_PONENS;
        proofTypes[5] = SExpressionConstants.REFLEXIVITY;
        proofTypes[6] = SExpressionConstants.SYMMETRY;
        proofTypes[7] = SExpressionConstants.TRANSITIVITY;
        proofTypes[8] = SExpressionConstants.TRANSITIVITY_STAR;
        proofTypes[9] = SExpressionConstants.MONOTONICITY;
        proofTypes[10] = SExpressionConstants.QUANT_INTRO;
        proofTypes[11] = SExpressionConstants.DISTRIBUTIVITY;
        proofTypes[12] = SExpressionConstants.AND_ELIM;
        proofTypes[13] = SExpressionConstants.NOT_OR_ELIM;
        proofTypes[14] = SExpressionConstants.REWRITE;
        proofTypes[15] = SExpressionConstants.REWRITE_STAR;
        proofTypes[16] = SExpressionConstants.PULL_QUANT;
        proofTypes[17] = SExpressionConstants.PULL_QUANT_STAR;
        proofTypes[18] = SExpressionConstants.PUSH_QUANT;
        proofTypes[19] = SExpressionConstants.ELIM_UNUSED_VARS;
        proofTypes[20] = SExpressionConstants.DER;
        proofTypes[21] = SExpressionConstants.QUANT_INST;
        proofTypes[22] = SExpressionConstants.HYPOTHESIS;
        proofTypes[23] = SExpressionConstants.LEMMA;
        proofTypes[24] = SExpressionConstants.UNIT_RESOLUTION;
        proofTypes[25] = SExpressionConstants.IFF_TRUE;
        proofTypes[26] = SExpressionConstants.IFF_FALSE;
        proofTypes[27] = SExpressionConstants.COMMUTATIVITY;
        proofTypes[28] = SExpressionConstants.AXIOM;
        proofTypes[29] = SExpressionConstants.INTRO;
        proofTypes[30] = SExpressionConstants.APPLY_DEF;
        proofTypes[31] = SExpressionConstants.IFF_OEQ;
        proofTypes[32] = SExpressionConstants.NNF_POS;
        proofTypes[33] = SExpressionConstants.NNF_NEG;
        proofTypes[34] = SExpressionConstants.NNF_STAR;
        proofTypes[35] = SExpressionConstants.CNF_STAR;
        proofTypes[36] = SExpressionConstants.SKOLEMIZE;
        proofTypes[37] = SExpressionConstants.MODUS_PONENS_OEQ;
        proofTypes[38] = SExpressionConstants.TH_LEMMA;
        proofTypes[39] = SExpressionConstants.TRANS;
        proofTypes[40] = SExpressionConstants.MP;
        return proofTypes;
    }
}
