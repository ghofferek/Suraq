/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.sexp;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.exceptions.NotATokenListException;
import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.parser.SExpParser;

/**
 * This class represents s-expressions. It consists of a list of subexpressions.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class SExpression {

    /**
     * the line number in the source file corresponding to this expression
     */
    protected int lineNumber = -1;

    /**
     * the column number in the source file corresponding to this expression
     */
    protected int columnNumber = -1;

    /**
     * The children of this (non-Token) S-expression.
     */
    private List<SExpression> children;

    /**
     * Constructs a new <code>SExpression</code>.
     * 
     * @param children
     *            the subexpressions.
     */
    public SExpression(List<? extends SExpression> children) {
        this.children = new ArrayList<SExpression>();
        this.children.addAll(children);
    }

    /**
     * Constructs a new <code>SExpression</code>.
     * 
     * @param children
     *            the subexpressions.
     */
    public SExpression(SExpression[] children) {
        this.children = new ArrayList<SExpression>();
        for (SExpression child : children)
            this.children.add(child);
    }

    /**
     * Constructs a new, empty <code>SExpression</code>.
     */
    public SExpression() {
        this.children = new ArrayList<SExpression>();
    }

    /**
     * Constructs a new <code>SExpression</code>, with only one child.
     * 
     * @param child
     *            the only child of this s-expression.
     */
    public SExpression(SExpression child) {
        this.children = new ArrayList<SExpression>();
        this.children.add(child);
    }

    /**
     * Convenience method to construct an <code>SExpression</code> with exactly
     * two children. Constructs a new <code>SExpression</code>.
     * 
     * @param first
     *            the first child
     * @param second
     *            the second child
     */
    public SExpression(SExpression first, SExpression second) {
        this.children = new ArrayList<SExpression>();
        this.children.add(first);
        this.children.add(second);
    }

    /**
     * Convenience method to construct an <code>SExpression</code> with exactly
     * three children. Constructs a new <code>SExpression</code>.
     * 
     * @param first
     *            the first child
     * @param second
     *            the second child
     * @param third
     *            the third child
     */
    public SExpression(SExpression first, SExpression second, SExpression third) {
        this.children = new ArrayList<SExpression>();
        this.children.add(first);
        this.children.add(second);
        this.children.add(third);
    }

    /**
     * 
     * Constructs a new <code>SExpression</code> by parsing the given String. If
     * <code>string</code> contains a single expression (or token), then this
     * single expression (token) is returned. If it contains a sequence of
     * expressions (tokens) then this sequence will be embedded into a root
     * expression.
     * 
     * @param string
     *            the <code>String</code> to be parsed.
     * @return the parsed expression, or <code>null</code> if parsing was
     *         unsuccessful;
     */
    public static SExpression fromString(String string) {
        SExpParser parser = new SExpParser(string);
        try {
            parser.parse();
        } catch (ParseError exc) {
            return null;
        }
        if (!parser.wasParsingSuccessfull())
            return null;
        List<SExpression> children = parser.getRootExpr().getChildren();
        if (children.size() == 1)
            return children.get(0);
        else
            return new SExpression(children);
    }

    /**
     * @return the size of this s-expression, i.e., the number of children. 0,
     *         if empty.
     */
    public int size() {
        return children.size();
    }

    /**
     * @return <code>true</code> if this s-expression is empty,
     *         <code>false</code> otherwise.
     */
    public boolean isEmpty() {
        return (children.size() == 0);
    }

    /**
     * Adds the given s-expression to the end of the list of children of this
     * one.
     * 
     * @param sexp
     *            the new child to add
     */
    public void addChild(SExpression sexp) {
        children.add(sexp);
    }

    /**
     * Adds the given s-expression to the children of this one, at the specified
     * position.
     * 
     * @param sexp
     *            the new child to add.
     * @param position
     *            the position of the new child.
     */
    public void addChild(SExpression sexp, int position) {
        children.add(position, sexp);
    }

    /**
     * Returns the list of children. This is the live list, not a copy.
     * 
     * @return the list of children (not a copy).
     */
    public List<SExpression> getChildren() {
        return children;
    }

    /**
     * Converts this s-expression into a list of <code>Token</code>s. Only
     * direct children will be considered. If this expression is empty, an empty
     * list will be returned. If one or more children are not <code>Token</code>
     * s, an exception is thrown.
     * 
     * @return A list of all <code>Token</code>s that are (direct) children of
     *         this expression.
     * @throws NotATokenListException
     *             if one or more children are not <code>Token</code>s.
     */
    public List<Token> toTokenList() throws NotATokenListException {
        List<Token> list = new ArrayList<Token>();
        if (isEmpty())
            return list;
        assert (children != null);

        for (int count = 0; count < children.size(); count++) {
            if (!(children.get(count) instanceof Token))
                throw new NotATokenListException(children.get(count).toString()
                        + " is not a Token!");
            else
                list.add((Token) children.get(count));
        }
        return list;
    }

    /**
     * Returns a pretty-printed string representation of this s-expression.
     * 
     * @return a pretty-printed string representation of this s-expression.
     */
    @Override
    public String toString() {
        if (isEmpty())
            return "()";

        if (size() == 1)
            return "(" + children.get(0).toString() + ")";

        StringBuffer buffer = new StringBuffer();
        buffer.append("(\n  ");
        for (SExpression child : children) {
            buffer.append((child instanceof Token ? child.toString() + "\n"
                    : child.toString() + ((child.size() > 1) ? "" : "\n"))
                    .replace("\n", "\n  "));
        }
        if (buffer.substring(buffer.length() - 2).equals("  "))
            buffer = buffer.delete(buffer.length() - 2, buffer.length());
        else
            buffer.append("\n");
        buffer.append(")\n");
        return buffer.toString();
    }

    /**
     * Recursively copies this s-expression.
     * 
     * @return a deep copy of this s-expression
     */
    public SExpression deepCopy() {
        SExpression copy = new SExpression();
        for (SExpression child : children) {
            copy.addChild(child.deepCopy());
        }
        return copy;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        boolean result = true;

        if (!(obj instanceof SExpression))
            return false;

        SExpression other = ((SExpression) obj);
        if (children.size() != other.children.size())
            return false;

        for (int count = 0; count < children.size(); count++)
            result = result
                    && children.get(count).equals(other.children.get(count));

        return result;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        int code = 0;
        for (int count = 0; count < children.size(); count++) {
            code = code ^ children.get(count).hashCode();
        }
        return code;
    }

    /**
     * @return the <code>lineNumber</code>
     */
    public int getLineNumber() {
        return lineNumber;
    }

    /**
     * @param <code>lineNumber</code> the new value for <code>lineNumber</code>
     */
    public void setLineNumber(int lineNumber) {
        this.lineNumber = lineNumber;
    }

    /**
     * @return the <code>columnNumber</code>
     */
    public int getColumnNumber() {
        return columnNumber;
    }

    /**
     * @param <code>columnNumber</code> the new value for
     *        <code>columnNumber</code>
     */
    public void setColumnNumber(int columnNumber) {
        this.columnNumber = columnNumber;
    }

    /**
     * Creates an SExpression for a function declaration. Produces something of
     * the form <code>(declare-fun name () type)</code>. If
     * <code>numParams > 0</code> the corresponding number if <code>Value</code>
     * parameters will be added. E.g. for <code>numParams==2</code>:
     * <code>(declare-fun name (Value Value) type)</code>.
     * 
     * @param name
     *            the name of the function
     * @param type
     *            the type of the function
     * @param numParams
     *            the number of parameters (all of type <code>Value</code>).
     *            Negative values will be treated as zero.
     * @return an <code>SExpression</code> declaring the specified function.
     */
    public static SExpression makeDeclareFun(Token name, SExpression type,
            int numParams) {
        SExpression result = new SExpression();
        result.addChild(SExpressionConstants.DECLARE_FUN);
        result.addChild(name);
        if (numParams > 0) {
            SExpression params = new SExpression();
            for (int count = 0; count < numParams; count++)
                params.addChild(SExpressionConstants.VALUE_TYPE);
            result.addChild(params);
        } else
            result.addChild(SExpressionConstants.EMPTY);
        result.addChild(type);
        return result;
    }
    
    /**
     * Checks an expression to be a valid proof type.
     * 
     * @param expr
     *            the expression to check
     * @return an <code>Boolean</code> value declaring iff expr is a valid proof type
     */    
    
    public  static Boolean isValidProofType(Token expr){
     	
    	for (SExpression proofType: SExpressionConstants.PROOF_TYPES) {
    		if (proofType.equals(expr))
    			return true;
    	}
    			
    			
    	return false; 
    }    

    /**
     * Creates the definition of proof types
     * 
     * @return an <code>SExpression[]</code> declaring the proof types.
     */
    
	public static SExpression[] createProofTypes() {
		// TODO Auto-generated method stub
		
		SExpression[] proofTypes = new SExpression[39];
		
		//see: z3_api.h
		proofTypes[0] = SExpression.fromString("undef");
		proofTypes[1] = SExpression.fromString("true");
		proofTypes[2] = SExpression.fromString("asserted");
		proofTypes[3] = SExpression.fromString("goal");
		proofTypes[4] = SExpression.fromString("modus-ponens");
		proofTypes[5] = SExpression.fromString("reflexivity");
		proofTypes[6] = SExpression.fromString("symmetry");
		proofTypes[7] = SExpression.fromString("transitivity");
		proofTypes[8] = SExpression.fromString("transitivity-star");
		proofTypes[9] = SExpression.fromString("monotonicity");
		proofTypes[10] = SExpression.fromString("quant-intro");
		proofTypes[11] = SExpression.fromString("distributivity");
		proofTypes[12] = SExpression.fromString("and-elim");
		proofTypes[13] = SExpression.fromString("not-or-elim");
		proofTypes[14] = SExpression.fromString("rewrite");
		proofTypes[15] = SExpression.fromString("rewrite-star");
		proofTypes[16] = SExpression.fromString("pull-quant");
		proofTypes[17] = SExpression.fromString("pull-quant-star");
		proofTypes[18] = SExpression.fromString("push-quant");
		proofTypes[19] = SExpression.fromString("elim-unused-vars");
		proofTypes[20] = SExpression.fromString("der");
		proofTypes[21] = SExpression.fromString("quant-inst");
		proofTypes[22] = SExpression.fromString("hypothesis");
		proofTypes[23] = SExpression.fromString("lemma");
		proofTypes[24] = SExpression.fromString("unit-resolution");
		proofTypes[25] = SExpression.fromString("iff-true");
		proofTypes[26] = SExpression.fromString("iff-false");
		proofTypes[27] = SExpression.fromString("commutativity");
		proofTypes[28] = SExpression.fromString("axiom");
		proofTypes[29] = SExpression.fromString("intro");
		proofTypes[30] = SExpression.fromString("apply-def");   
		proofTypes[31] = SExpression.fromString("iff-oeq");
		proofTypes[32] = SExpression.fromString("nnf-pos");
		proofTypes[33] = SExpression.fromString("nnf-neg");
		proofTypes[34] = SExpression.fromString("nnf-star");
		proofTypes[35] = SExpression.fromString("cnf-star");
		proofTypes[36] = SExpression.fromString("skolemize");
		proofTypes[37] = SExpression.fromString("modus-pones-oeq");
		proofTypes[38] = SExpression.fromString("th-lemma");
		
		return proofTypes;
	}
}
