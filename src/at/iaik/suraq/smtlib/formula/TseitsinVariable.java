/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.Set;

import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class TseitsinVariable extends PropositionalVariable {

    /**
     * The formula this Tseitsin variable represents.
     */
    private final Formula expansion;

    /**
     * 
     * Constructs a new <code>TseitsinVariable</code>.
     * 
     * @param varName
     *            the name of the variable
     * @param expansion
     *            the formula it represents
     */
    public TseitsinVariable(String varName, Formula expansion) {
        this(new Token(varName), expansion);
    }

    public TseitsinVariable(Token varName, Formula expansion) {
        super(varName);
        this.expansion = expansion.deepFormulaCopy();
        assert (this.expansion.getPartitionsFromSymbols().size() == 1 || (this.expansion
                .getPartitionsFromSymbols().size() == 1 && this.expansion
                .getPartitionsFromSymbols().contains(-1)));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.PropositionalVariable#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof TseitsinVariable))
            return false;
        assert (obj instanceof TseitsinVariable);
        return (this.varName.equals(((TseitsinVariable) obj).varName) && this.expansion
                .equals(((TseitsinVariable) obj).expansion));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.PropositionalVariable#hashCode()
     */
    @Override
    public int hashCode() {
        return varName.hashCode() ^ expansion.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.PropositionalVariable#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return new TseitsinVariable(new String(varName),
                expansion.deepFormulaCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.PropositionalVariable#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return this.deepTermCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.PropositionalVariable#getPartitionsFromSymbols()
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        return expansion.getPartitionsFromSymbols();
    }

}
