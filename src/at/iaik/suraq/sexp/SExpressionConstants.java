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

    public static final SExpression SET_LOGIC_QF_AUFLIA = SExpression
            .fromString("(set-logic QF_AUFLIA)");

    public static final SExpression SET_OPTION_PRODUCE_INTERPOLANT = SExpression
            .fromString("(set-option :produce-interpolants true)");

    public static final SExpression SET_OPTION_PROPAGATE_BOOLEANS_FALSE = SExpression
            .fromString("(set-option :propagate-booleans false)");

    public static final SExpression SET_OPTION_PROPAGATE_VALUES_FALSE = SExpression
            .fromString("(set-option :propagate-values false)");

    public static final SExpression SET_OPTION_PRODUCE_MODELS_TRUE = SExpression
            .fromString("(set-option :produce-models true)");

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

    public static final SExpression APPLY_TSEITIN = SExpression
            .fromString("(apply (then (! simplify :elim-and true) (! simplify :elim-and true) tseitin-cnf))");

    public static final Token SIMPLIFY = (Token) SExpression
            .fromString("simplify");

    public static final Token ELIM_AND = (Token) SExpression
            .fromString(":elim-and");

    public static final Token UNSAT = (Token) SExpression.fromString("unsat");

    public static final Token LET = (Token) SExpression.fromString("let");

    public static final Token UNDEF = (Token) SExpression.fromString("undef");
    public static final Token ASSERTED = (Token) SExpression
            .fromString("asserted");
    public static final Token GOAL = (Token) SExpression.fromString("goal");
    public static final Token GOALS = (Token) SExpression.fromString("goals");
    public static final Token MODUS_PONENS = (Token) SExpression
            .fromString("mp");
    public static final Token REFLEXIVITY = (Token) SExpression
            .fromString("reflexivity");
    public static final Token SYMMETRY = (Token) SExpression.fromString("symm");
    public static final Token TRANSITIVITY = (Token) SExpression
            .fromString("trans");
    public static final Token TRANSITIVITY_STAR = (Token) SExpression
            .fromString("transitivity-star");
    public static final Token MONOTONICITY = (Token) SExpression
            .fromString("monotonicity");
    public static final Token QUANT_INTRO = (Token) SExpression
            .fromString("|quant-intro|");
    public static final Token DISTRIBUTIVITY = (Token) SExpression
            .fromString("distributivity");
    public static final Token AND_ELIM = (Token) SExpression
            .fromString("|and-elim|");
    public static final Token NOT_OR_ELIM = (Token) SExpression
            .fromString("|not-or-elim|");
    public static final Token REWRITE = (Token) SExpression
            .fromString("rewrite");
    public static final Token REWRITE_STAR = (Token) SExpression
            .fromString("rewrite-star");
    public static final Token PULL_QUANT = (Token) SExpression
            .fromString("|pull-quant|");
    public static final Token PULL_QUANT_STAR = (Token) SExpression
            .fromString("|pull-quant-star|");
    public static final Token PUSH_QUANT = (Token) SExpression
            .fromString("|push-quant|");
    public static final Token ELIM_UNUSED_VARS = (Token) SExpression
            .fromString("|elim-unused-vars|");
    public static final Token DER = (Token) SExpression.fromString("der");
    public static final Token QUANT_INST = (Token) SExpression
            .fromString("|quant-inst|");
    public static final Token HYPOTHESIS = (Token) SExpression
            .fromString("hypothesis");
    public static final Token LEMMA = (Token) SExpression.fromString("lemma");
    public static final Token UNIT_RESOLUTION = (Token) SExpression
            .fromString("|unit-resolution|");
    public static final Token RESOLUTION = (Token) SExpression
            .fromString("resolution");
    public static final Token IFF_TRUE = (Token) SExpression
            .fromString("|iff-true|");
    public static final Token IFF_FALSE = (Token) SExpression
            .fromString("|iff-false|");
    public static final Token COMMUTATIVITY = (Token) SExpression
            .fromString("commutativity");
    public static final Token AXIOM = (Token) SExpression
            .fromString("|def-axiom|");
    public static final Token INTRO = (Token) SExpression.fromString("intro");
    public static final Token APPLY_DEF = (Token) SExpression
            .fromString("|apply-def|");
    public static final Token IFF_OEQ = (Token) SExpression
            .fromString("iff-oeq");
    public static final Token NNF_POS = (Token) SExpression
            .fromString("nnf-pos");
    public static final Token NNF_NEG = (Token) SExpression
            .fromString("nnf-neg");
    public static final Token NNF_STAR = (Token) SExpression
            .fromString("nnf-star");
    public static final Token CNF_STAR = (Token) SExpression
            .fromString("cnf-star");
    public static final Token SKOLEMIZE = (Token) SExpression
            .fromString("skolemize");
    public static final Token MODUS_PONENS_OEQ = (Token) SExpression
            .fromString("modus-pones-oeq");
    public static final Token TH_LEMMA = (Token) SExpression
            .fromString("th-lemma");

    // added by chillebold on 06.07.2012
    public static final Token SIMPLEPROOF = (Token) SExpression
            .fromString("proof");

    public static final Token TRANS = (Token) SExpression.fromString("trans");
    public static final Token MP = (Token) SExpression.fromString("mp");
    public static final Token[] PROOF_TYPES = SExpressionConstants
            .createProofTypes();

    /**
     * Creates the definition of proof types
     * 
     * @return an <code>SExpression[]</code> declaring the proof types.
     */

    public static Token[] createProofTypes() {

        // number modified by chillebold on 06.07.2012
        Token[] proofTypes = new Token[40];

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

        // added by chillebold on 06.07.2012
        proofTypes[39] = SExpressionConstants.SIMPLEPROOF;
        return proofTypes;
    }
}
