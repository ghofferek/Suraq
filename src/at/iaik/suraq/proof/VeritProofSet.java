package at.iaik.suraq.proof;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.util.ImmutableArrayList;

/**
 * VeritProofSet is a single set-line in the proof. You shall not use this class
 * to create or modify the proof. Use VeritProof instead. To prevent you from
 * using certain functions, they are marked as deprecated.
 * 
 * @author chillebold
 * 
 */
public class VeritProofSet {
    private final String name;
    private final String type;
    private final List<Formula> conclusions;
    private final List<VeritProofSet> clauses;
    private final Integer iargs;
    private final List<VeritProofSet> parents = new ArrayList<VeritProofSet>();

    /**
     * Do not call this constructor by yourself. Use VeritProof to create this
     * class.
     * 
     * @param name
     * @param type
     * @param conclusions
     * @param clauses
     * @param iargs
     */
    @Deprecated
    protected VeritProofSet(String name, String type,
            List<Formula> conclusions, List<VeritProofSet> clauses,
            Integer iargs) {
        this.name = name;
        this.type = type;
        this.conclusions = conclusions == null ? null : new ArrayList<Formula>(
                conclusions);
        this.clauses = clauses == null ? null : new ArrayList<VeritProofSet>(
                clauses);
        this.iargs = iargs;
    }

    public String getName() {
        return name;
    }

    public String getType() {
        return type;
    }

    /**
     * This method returns the inner conclusions-List. If you modify elements in
     * this list or the list itself, also this object changes! Notice the method
     * getConclusionCopy()
     * 
     * @return
     */
    public List<Formula> getConclusion() {
        return conclusions;
    }

    /**
     * This method returns a copy of the inner conclusions-List.
     * 
     * @return a copied ArrayList of the conclusions
     */
    public List<Formula> getConclusionCopy() {
        return new ArrayList<Formula>(conclusions);
    }

    /**
     * returns an immutable copy of clauses. You cannot modify the list
     * direclty. Use the VeritProof-Class instead!
     * 
     * @return
     */
    public ImmutableArrayList<VeritProofSet> getClauses() {
        return new ImmutableArrayList<VeritProofSet>(clauses);
    }

    public Integer getIargs() {
        return iargs;
    }

    /**
     * returns an immutable copy of parents. You cannot modify the list
     * directly. Use the VeritProof-Class instead!
     * 
     * @return
     */
    public ImmutableArrayList<VeritProofSet> getParents() {
        return new ImmutableArrayList<VeritProofSet>(parents);
    }

    @Deprecated
    protected void addParent(VeritProofSet parent) {
        parents.add(parent);
    }

    @Deprecated
    protected boolean removeParent(VeritProofSet parent) {
        return parents.remove(parent);
    }

    @Deprecated
    protected void addClause(VeritProofSet clause) {
        clauses.add(clause);
    }

    @Deprecated
    protected boolean removeClause(VeritProofSet clause) {
        return clauses.remove(clause);
    }

    @Override
    public String toString() {
        String str = "(set " + name + " (" + type;
        if (clauses != null) {
            str += " :clauses (";
            for (VeritProofSet clause : clauses)
                str += clause.getName() + " ";
            str += ")";
        }
        if (iargs != null) {
            str += " :iargs (" + iargs + ")";
        }
        if (conclusions != null) {
            str+=" :conclusions (";
            for (Formula conclusion : conclusions)
                str += " " + conclusion.toString();
            str+=")";
        }
        str += "))";
        return str;
    }

}
