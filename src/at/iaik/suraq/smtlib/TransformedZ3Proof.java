/**
 * Author: Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib;

import java.util.List;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;

/**
 * @author Bettina Koenighofer <bettina.koenighofer@iaik.tugraz.at>
 * 
 * Should only contain the following proof rules: 
 * 		Asserted, Symmetrie, Transitivity, Monotonicity and (simple) Resolution.
 * 
 * Formulas for consequents should have the following structure:
 * 		- each atom is either a positive equality of two terms, a propositional variable,
 * 			or an uninterpreted predicate
 * 		- each literal is either an atom or a negation of an atom
 * 		- formula is always an or formula which consists of at least one literal
 * 		
 * Formulas for literals should be positive atoms as defined above. 
 */
public class TransformedZ3Proof extends Z3Proof {
	
    /**
     * Specifies if this proof object is an axiom introduced during transformation.
     */
    private boolean isAxiom = false;
	
	public TransformedZ3Proof(Z3Proof z3proof) {
		
		// FIXME
		super(null, null, null);
	}
	   
	
	public TransformedZ3Proof(Token proofType, List<TransformedZ3Proof> subProofs,
			Formula proofFormula) {
		super(proofType, subProofs, proofFormula);
		// TODO Auto-generated constructor stub
	}
	
	public void toLocalResolutionProof() {
		
	}
	
	
}