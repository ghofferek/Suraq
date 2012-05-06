package at.iaik.suraq.smtlib;

import java.util.Set;

import at.iaik.suraq.sexp.SExpression;

public interface SMTLibObject {

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    public Set<Integer> getAssertPartition(); 
    
    /**
     * Converts this formula into an s-expression compatible with SMTLIBv2. Only
     * the formula itself is converted. No variable/function/macro declarations
     * are included.
     * 
     * @return this formulas as an SMTLIBv2 s-expression.
     */
    public SExpression toSmtlibV2();
    
    /**
     * 
     * @return a String representation of this formula
     */
    @Override
    public String toString();
}
