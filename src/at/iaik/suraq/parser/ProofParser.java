/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.formula.AndFormula;
import at.iaik.suraq.formula.ArrayVariable;
import at.iaik.suraq.formula.DomainVariable;
import at.iaik.suraq.formula.Formula;
import at.iaik.suraq.formula.ProofFormula;
import at.iaik.suraq.formula.PropositionalVariable;
import at.iaik.suraq.formula.Term;
import at.iaik.suraq.formula.UninterpretedFunction;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ProofParser extends SMTLibParser {

	
    
    /**
     * 
     * Constructs a new <code>ProofParser</code>.
     * 
     * @param root
     *            the root expression to parse.
     * @param domainVars
     * 			  proof domain variables
     * @param propsitionalVars
     * 			  proof propositional variables          
     * @param arrayVars
     * 			  proof array variables
     * @param uninterpretedFunctions
     * 			  proof uninterpreted Functions
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
		
		//testparsing
		/*
        this.functions.add(new UninterpretedFunction("f",1,new Token("Value")));
        this.domainVariables.add(new DomainVariable("x"));       
        this.domainVariables.add(new DomainVariable("y"));  
        this.domainVariables.add(new DomainVariable("z"));  */
	}
	
    /**
     * 
     * @return a (deep) copy of the root expression of this parser.
     */
    public SExpression getRootExpr() {
        return rootExpr.deepCopy();
    }	
    
    /**
     * Parses the root s-expression into a formula, which can then be retrieved
     * using <code>getFormula</code>.
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
                throw new ParseError(expression.getLineNumber(),
                        expression.getColumnNumber(), expression.toString(),
                        "Expected 'proof' or 'let' expression.");
                       
            if (isLet(expression)) {
                handleLet(expression);
                continue;
            }

            else if (isProof(expression)){
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
     * Handles an let expression. I.e., if <code>mainFormula</code> is still
     * <code>null</code>, it will be initialized to the result of parsing this
     * assert statement's body. If <code>mainFormula</code> already is non-
     * <code>null</code>, a conjunction of its current value an the parsed body
     * will be made.
     * 
     * @param expression
     *            the assert expression to parse.
     */
    private void handleLet(SExpression expression) throws ParseError {
    	
    	//(let (($x5 (or a c))) scope)  
        
        Token key = (Token) expression.getChildren().get(1).getChildren().get(0).getChildren().get(0);
        SExpression entryExpr = expression.getChildren().get(1).getChildren().get(0).getChildren().get(1);
        
        insertLUTEntry(key, entryExpr);
          
        SExpression scopeExpr = expression.getChildren().get(2);
        Formula scope = parseBody(scopeExpr);                  

        if (mainFormula == null)
            mainFormula = scope;
        else {
            List<Formula> list = new ArrayList<Formula>();
            list.add(mainFormula); 
            list.add(scope); 
            mainFormula = new AndFormula(list);
        }
    }
    

    /**
     * Handles an proof expression. I.e., if <code>mainFormula</code> is still
     * <code>null</code>, it will be initialized to the result of parsing this
     * assert statement's body. If <code>mainFormula</code> already is non-
     * <code>null</code>, a conjunction of its current value an the parsed body
     * will be made.
     * 
     * @param expression
     *            the assert expression to parse.
     */
    private void handleProof(SExpression expression) throws ParseError {
        //(asserted @x38 @x35 $x11) oder (asserted (hypothesis $x7) @x35 (or a c))
        
    	assert(expression.getChildren().get(0) instanceof Token);
    	
    	Token proofType = (Token) expression.getChildren().get(0);
        
        int numChildren =  expression.getChildren().size();
        assert(numChildren<=2);
        
        int subProofsCount = numChildren-2; //first child is proofType, last one is proofFormula       
        List<ProofFormula> subProofs = new ArrayList<ProofFormula>();
        if (subProofsCount>0)
        	for (int i=1; i<=subProofsCount; i++) {
        	    	subProofs.add(parseProofBody(expression.getChildren().get(i)));
        		}
        
        SExpression proofFormulaExpr = expression.getChildren().get(numChildren-1);
        Formula proofFormula = parseFormulaBody(proofFormulaExpr);
        
        ProofFormula formula = new ProofFormula(proofType, subProofs, proofFormula);

        if (mainFormula == null)
            mainFormula = formula;
        else {
            List<Formula> list = new ArrayList<Formula>();
            list.add(mainFormula); 
            list.add(formula); 
            mainFormula = new AndFormula(list);
        }
    }     
    
    
    /**
     * Inserts an expression into a lookup-table.
     * 
     * @param entryExpr
     *            the expression to be inserted into the 
     *            lookup-table (proofs, formulas or terms).
     * @throws ParseError 
     */
  
    private void insertLUTEntry(Token key, SExpression entryExpr) throws ParseError {
    	
        Token pureKey = new Token (key.toString().substring(1));
        char typeCharEntry = entryExpr.toString().charAt(0);
        
        if (isProof(entryExpr)) {
            if(typeCharEntry==REF_PROOF)
            	throw new ParseError(entryExpr,
                    "no assignment of proof to another reference of proof");        	
        	ProofFormula entry = parseProofBody(entryExpr);
        	this.proofs.put(pureKey, entry);
        }       
        else if (isFormula(entryExpr)) {        	
            if(typeCharEntry==REF_FORMULA)
            	throw new ParseError(entryExpr,
                    "no assignment of formula to another reference of formula");
 
        	Formula entry = parseFormulaBody(entryExpr);         	
            this.formulas.put(pureKey, entry);
        }
        else if (isTerm(entryExpr)) {
            if(typeCharEntry==REF_TERM)
            	throw new ParseError(entryExpr,
                    "no assignment of term to another reference of term");    
            
        	Term entry  = parseTerm(entryExpr);
        	this.terms.put(pureKey, entry);
        }
        else throw new ParseError(entryExpr,
                "unknown expression type found"); 
    }    
    
    
	
    /**
     * Checks whether the given expression is an proof instance.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is an proof
     *         expression, <code>false</code> otherwise.
     */
    
    //(asserted @x38 @x35 $x11) oder (asserted (hypothesis $x7) @x35 (or a c)) oder @38
    
    private boolean isProof(SExpression expression) {
    
        if (expression instanceof Token) {
            if (REF_PROOF == expression.toString().charAt(0))
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
     * Checks whether the given expression is a term
     * 
     * @param expression
     *            the expression to check
     * @return <code>true</code> if the given expression is a term,
     *         <code>false</code> otherwise.
     */
    private boolean isTerm(SExpression expression) {
    	
    	if (isDomainVariable(expression))
    		return true;
    	
    	if (isArrayVariable(expression))
    		return true;
        
    	if (REF_PROOF == expression.toString().charAt(0))
        	return true;
        
        if (isUninterpredFunctionInstance(expression)!=null)
        	return true;
        	
        	
    	return false;
    }     
    
   
    
    
    /**
     * Checks whether the given expression is an formula instance.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is an formula
     *         expression, <code>false</code> otherwise.
     */    
    private boolean isFormula(SExpression expression) {

        if (REF_FORMULA == expression.toString().charAt(0))
            return true;
        
        if (isPropositionalConstOrVar(expression)) //true, false, a, ...
            return true;
    	
        Token formulaType = (Token) expression.getChildren().get(0);      
        if (SExpression.isValidFormulaType(formulaType))   //and, or, not, =, ...
        	return true;

        return false;
    }   
    
    
    /**
     * Checks whether the given expression is an let instance.
     * 
     * @param expression
     *            the expression to check.
     * @return <code>true</code> if the given expression is an let
     *         expression, <code>false</code> otherwise.
     */
    
    private boolean isLet(SExpression expression) {
    	
    	//(let (($x5 (or a c)) scope)
        if (expression instanceof Token)
            return false;
        if (expression.getChildren().size() != 3)
            return false;
        if (!(expression.getChildren().get(0) instanceof Token))  //let
            return false;
        assert (expression.getChildren().get(0) instanceof Token);
        if (!(expression.getChildren().get(0).equals(SExpressionConstants.LET)))
            return false;
        
        Token key = (Token) expression.getChildren().get(1).getChildren().get(0).getChildren().get(0); //$x5
        if (!(key instanceof Token))  
            return false;
            
         if (key.toString().charAt(0)!= REF_PROOF 
            	&& key.toString().charAt(0)!= REF_FORMULA
            	&& key.toString().charAt(0)!= REF_TERM)
            return false;        	
                           
        return true;
    }

  
    

    /**
     * Parses a given s-expression into a formula.
     * The s-expression can either be of a proof 
     * formula or a let-assignment.
     * 
     * @param expression
     *            the expression to parse.
     * @return the formula resulting from the given expression.
     * @throws ParseError
     *             if parsing fails.
     */
    private Formula parseBody(SExpression expression) throws ParseError {
    	if (isLet(expression))
    		return parseLet(expression);
    	else if (isFormula(expression))
    		return parseFormulaBody(expression);
    	else if (isProof(expression))
    		return (parseProofBody(expression));
    	else throw new ParseError(expression,
    			"parseBody can only parse Let-Expression, Formula or Proof-Formulas!");
    }
   
    
    /**
     * Handles an let expression. I.e., if <code>mainFormula</code> is still
     * <code>null</code>, it will be initialized to the result of parsing this
     * assert statement's body. If <code>mainFormula</code> already is non-
     * <code>null</code>, a conjunction of its current value an the parsed body
     * will be made.
     * 
     * @param expression
     *            the assert expression to parse.
     * @return the formula resulting from parsing. 
     */
    private Formula parseLet(SExpression expression) throws ParseError {
    	  
        
        Token key = (Token) expression.getChildren().get(1).getChildren().get(0).getChildren().get(0);
        SExpression entryExpr = expression.getChildren().get(1).getChildren().get(0).getChildren().get(1);
        
        insertLUTEntry(key, entryExpr);
          
        SExpression scopeExpr = expression.getChildren().get(2);
        Formula scope = parseBody(scopeExpr);                  

        return scope;
    }
    
    

    /**
     * Parses a given s-expression into a <code>ProofFormula</code>.
     * 
     * @param expression
     *            the expression to parse.
     * @return the formula resulting from the given expression.
     * @throws ParseError
     *             if parsing fails.
     */
    private ProofFormula parseProofBody(SExpression expression) throws ParseError {
    	
    	if (expression.toString().charAt(0)== REF_PROOF) {
    		//resolve reference with LUT
    		assert(expression instanceof Token);
    		Token pureKey = new Token (expression.toString().substring(1));
    		ProofFormula formula = this.proofs.get(pureKey);
    		
    		if (formula==null)
    			throw new ParseError(expression,
    					"could not find a matching proof-LUT-entry!");
    		
    		return formula;
    	} 
    	else {
    		assert(expression.getChildren().get(0) instanceof Token);
            Token proofType = (Token) expression.getChildren().get(0);
            
            int numChildren =  expression.getChildren().size();
            assert(numChildren<=2);
            
            int subProofsCount = numChildren-2; //first child is proofType, last one is proofFormula       
            List<ProofFormula> subProofs = new ArrayList<ProofFormula>();
            if (subProofsCount>0)
            	for (int i=1; i<=subProofsCount; i++) {
            	    	subProofs.add(parseProofBody(expression.getChildren().get(i)));
            		}
            
            SExpression proofFormulaExpr = expression.getChildren().get(numChildren-1);
            Formula proofFormula = parseFormulaBody(proofFormulaExpr);
            
            return new ProofFormula(proofType, subProofs, proofFormula);   		
    	}

    }
    
    
    
   
    
    
    
}
