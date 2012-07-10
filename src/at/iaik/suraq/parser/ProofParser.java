/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.Z3Proof;
import at.iaik.suraq.smtlib.formula.ArrayVariable;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.Term;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ProofParser extends SMTLibParser {

    /**
     * The proof that results from parsing.
     */
    protected Z3Proof rootProof = null;

    /**
     * 
     * Constructs a new <code>ProofParser</code>.
     * 
     * @param root
     *            the root expression to parse.
     * @param domainVars
     *            proof domain variables
     * @param propsitionalVars
     *            proof propositional variables
     * @param arrayVars
     *            proof array variables
     * @param uninterpretedFunctions
     *            proof uninterpreted Functions
     */
    public ProofParser(SExpression root, Set<DomainVariable> domainVars,
            Set<PropositionalVariable> propsitionalVars,
            Set<ArrayVariable> arrayVars,
            Set<UninterpretedFunction> uninterpretedFunctions) {

        this.boolVariables = propsitionalVars;
        this.arrayVariables = arrayVars;
        this.domainVariables = domainVars;
        this.functions = uninterpretedFunctions;
        this.rootExpr = root;

    }

    /**
     * 
     * @return a (deep) copy of the root expression of this parser.
     */
    public SExpression getRootExpr() {
        return rootExpr.deepCopy();
    }

    /**
     * Parses the root s-expression into a proof, which can then be retrieved
     * using <code>getRootProof</code>.
     * 
     * @see at.iaik.suraq.parser.Parser#parse()
     */
    @Override
    public void parse() throws ParseError {

        for (int count = 0; count < rootExpr.getChildren().size(); count++) {
            SExpression expression = rootExpr.getChildren().get(count);

            if (expression instanceof Token)
                throw new ParseError(expression.getLineNumber(),
                        expression.getColumnNumber(), expression.toString(),
                        "Unexpected Token.");

            if (expression.getChildren().size() == 0)
                throw new ParseError(expression.getLineNumber(),
                        expression.getColumnNumber(), expression.toString(),
                        "Unexpected empty expression.");

            assert (expression.getChildren().size() >= 1);

            // at this point, we expect a proof expression or an let expression

            if (!(expression.getChildren().get(0) instanceof Token))
            {
                if(expression.getChildren().get(0).equals(SExpressionConstants.SET_LOGIC_QF_UF))
                {
                    System.out.println("Expected 'proof' or 'let' expression. Got: "+
                        expression.getChildren().get(0).getClass().getName()+
                        " \nwith value: "+expression.getChildren().get(0).toString());
                    System.out.println("use next: "+expression.getChildren().get(1).getClass().getName());
                    
                    expression = expression.getChildren().get(1); // this is now a (PROOF
                    // also leave out the PROOF...
                    expression = expression.getChildren().get(1); // this is now the first LET
                    
                   
                }
                else
                {
                    System.err.println("Expected 'proof' or 'let' expression. Got: "+
                            expression.getChildren().get(0).getClass().getName()+
                            " \nwith value: "+expression.getChildren().get(0).toString());
                    throw new ParseError(expression.getLineNumber(),
                            expression.getColumnNumber(), expression.toString(),
                            "Expected 'proof' or 'let' expression.");
                }
            }

            if (isLet(expression)) {
                handleLet(expression);
                continue;
            }

            else if (isProof(expression)) {
                handleProof(expression);
                continue;

            }

            // we got something unexpected, if we reach this point.
            throw new ParseError(expression.getLineNumber(),
                    expression.getColumnNumber(), expression.toString(),
                    "Expected 'proof' or 'let' expression.");
        }

        parsingSuccessfull = true;
    }

    /**
     * Handles an let expression. I.e., if <code>rootProof</code> is still
     * <code>null</code>, it will be initialized to the result of parsing this
     * assert statement's body. If <code>rootProof</code> already is non-
     * <code>null</code>, a conjunction of its current value an the parsed body
     * will be made.
     * 
     * @param expression
     *            the assert expression to parse.
     */
    private void handleLet(SExpression expression) throws ParseError {

        Token key = (Token) expression.getChildren().get(1).getChildren()
                .get(0).getChildren().get(0);
        SExpression entryExpr = expression.getChildren().get(1).getChildren()
                .get(0).getChildren().get(1);

        insertLUTEntry(key, entryExpr);

        SExpression scopeExpr = expression.getChildren().get(2);
        Z3Proof scope = parseBody(scopeExpr);

        if (rootProof == null)
            rootProof = scope;
        else {
            throw new RuntimeException("Found more than one proof, aborting.");
        }
    }

    /**
     * Handles an proof expression. I.e., if <code>rootProof</code> is still
     * <code>null</code>, it will be initialized to the result of parsing this
     * assert statement's body. If <code>rootProof</code> already is non-
     * <code>null</code>, a conjunction of its current value an the parsed body
     * will be made.
     * 
     * @param expression
     *            the assert expression to parse.
     */
    private void handleProof(SExpression expression) throws ParseError {

        assert (expression.getChildren().get(0) instanceof Token);

        Token proofType = (Token) expression.getChildren().get(0);

        int numChildren = expression.getChildren().size();
        assert (numChildren >= 2);

        int subProofsCount = numChildren - 2;

        List<Z3Proof> subProofs = new ArrayList<Z3Proof>();
        if (subProofsCount > 0)
            for (int i = 1; i <= subProofsCount; i++) {
                subProofs.add(parseBody(expression.getChildren().get(i)));
            }

        SExpression consequentExpr = expression.getChildren().get(
                numChildren - 1);
        Formula consequent = null;
        try{
            consequent = parseFormulaBody(consequentExpr);
        }catch(ParseError ex)
        {
            System.err.println("Exception in ProofParser:handleProof on parseFormulaBody: "+ex.getMessage());
            ex.printStackTrace();
            System.exit(0); // TODO: remove System.exit(0)
            throw ex;            
        }
        Z3Proof proof = new Z3Proof(proofType, subProofs, consequent);

        if (rootProof == null)
            rootProof = proof;
        else {
            throw new RuntimeException("Found more than one proof, aborting.");
        }
    }

    /**
     * Inserts an expression into a lookup-table.
     * 
     * @param entryExpr
     *            the expression to be inserted into the lookup-table (proofs,
     *            formulas or terms).
     * @throws ParseError
     */

    private void insertLUTEntry(Token key, SExpression entryExpr)
            throws ParseError {

        Token pureKey = new Token(key.toString().substring(1));
        char typeCharEntry = entryExpr.toString().charAt(0);
        char typeCharKey = key.toString().charAt(0);

        if (typeCharKey == SMTLibParser.REF_PROOF) {
            if (typeCharEntry == SMTLibParser.REF_PROOF)
                throw new ParseError(entryExpr,
                        "no assignment of proof to another reference of proof");

            Z3Proof entry = parseBody(entryExpr);
            this.proofs.put(pureKey, entry);
        } else if (typeCharKey == SMTLibParser.REF_FORMULA) {
            if (typeCharEntry == SMTLibParser.REF_FORMULA)
                throw new ParseError(entryExpr,
                        "no assignment of formula to another reference of formula");

            Formula entry = parseFormulaBody(entryExpr);
            // if (!Util.isLiteral(entry))
            // entry = new TseitsinVariable(key, entry);
            this.formulas.put(pureKey, entry);
        } else if (typeCharKey == SMTLibParser.REF_TERM) {
            if (typeCharEntry == SMTLibParser.REF_TERM)
                throw new ParseError(entryExpr,
                        "no assignment of term to another reference of term");

            Term entry = parseTerm(entryExpr);
            this.terms.put(pureKey, entry);
        } else
            throw new ParseError(entryExpr, "unknown expression type found");
    }

    /**
     * Checks whether the given expression is an proof instance.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is an proof expression,
     *         <code>false</code> otherwise.
     */

    private boolean isProof(SExpression expression) {

        if (expression instanceof Token) {
            if (SMTLibParser.REF_PROOF == expression.toString().charAt(0))
                return true;
            else
                return false;
        }

        if (!(expression.getChildren().size() >= 2))
            return false;
        if (!(expression.getChildren().get(0) instanceof Token))
            return false;
        assert (expression.getChildren().get(0) instanceof Token);

        Token proofType = (Token) expression.getChildren().get(0);

        if (!SExpression.isValidProofType(proofType))
            return false;

        return true;
    }

    /**
     * Checks whether the given expression is an let instance, with a key that
     * starts either with $, @, or ?.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is an let expression,
     *         <code>false</code> otherwise.
     */
    @Override
    protected boolean isLet(SExpression expression) {

        if (!super.isLet(expression))
            return false;

        Token key = (Token) expression.getChildren().get(1).getChildren()
                .get(0).getChildren().get(0); // $x5

        if (key.toString().charAt(0) != SMTLibParser.REF_PROOF
                && key.toString().charAt(0) != SMTLibParser.REF_FORMULA
                && key.toString().charAt(0) != SMTLibParser.REF_TERM)
            return false;

        return true;
    }

    /**
     * Parses a given s-expression into a proof. The s-expression can either be
     * of a proof or a let-assignment.
     * 
     * @param expression
     *            the expression to parse.
     * @return the proof resulting from the given expression.
     * @throws ParseError
     *             if parsing fails.
     */
    private Z3Proof parseBody(SExpression expression) throws ParseError {
        if (isLet(expression))
            return parseLet(expression);
        else if (isProof(expression))
            return (parseProofBody(expression));
        else
            throw new ParseError(expression,
                    "parseBody can only parse Let-Expression or Proof!");
    }

    /**
     * Handles an let expression.
     * 
     * @param expression
     *            the let expression to parse.
     * @return the proof resulting from parsing.
     */
    private Z3Proof parseLet(SExpression expression) throws ParseError {

        Token key = (Token) expression.getChildren().get(1).getChildren()
                .get(0).getChildren().get(0);
        SExpression entryExpr = expression.getChildren().get(1).getChildren()
                .get(0).getChildren().get(1);

        insertLUTEntry(key, entryExpr);

        SExpression scopeExpr = expression.getChildren().get(2);
        Z3Proof scope = parseBody(scopeExpr);

        return scope;
    }

    /**
     * Parses a given s-expression into a <code>Z3Proof</code>.
     * 
     * @param expression
     *            the expression to parse.
     * @return the formula resulting from the given expression.
     * @throws ParseError
     *             if parsing fails.
     */
    private Z3Proof parseProofBody(SExpression expression) throws ParseError {

        if (expression.toString().charAt(0) == SMTLibParser.REF_PROOF) {
            // resolve reference with LUT
            assert (expression instanceof Token);
            Token pureKey = new Token(expression.toString().substring(1));
            Z3Proof formula = this.proofs.get(pureKey);

            if (formula == null)
                throw new ParseError(expression,
                        "could not find a matching proof-LUT-entry!");

            return formula;
        } else {
            assert (expression.getChildren().get(0) instanceof Token);
            Token proofType = (Token) expression.getChildren().get(0);

            int numChildren = expression.getChildren().size();

            int subProofsCount = numChildren - 2; // first child is proofType,
                                                  // last one is consequent
            List<Z3Proof> subProofs = new ArrayList<Z3Proof>();
            if (subProofsCount > 0)
                for (int i = 1; i <= subProofsCount; i++) {
                    subProofs.add(parseBody(expression.getChildren().get(i)));
                }

            SExpression consequentExpr = expression.getChildren().get(
                    numChildren - 1);
            Formula consequent = parseFormulaBody(consequentExpr);

            return new Z3Proof(proofType, subProofs, consequent);
        }

    }

    /**
     * Returns the root proof that resulted from parsing, or <code>null</code>
     * if parsing was not successful.
     * 
     * @return the proof that resulted from parsing, or <code>null</code> if
     *         parsing was not successful.
     */
    public Z3Proof getRootProof() {
        if (!wasParsingSuccessfull())
            return null;
        return rootProof;
    }
}
