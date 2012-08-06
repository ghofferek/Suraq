package at.iaik.suraq.proof;

import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.util.ImmutableArrayList;

public class VeritProofSet {
    protected final String name;
    protected final String type;
    protected final List<Formula> conclusions;
    protected final List<VeritProofSet> clauses;
    protected final Integer iargs;
    protected final List<VeritProofSet> parents = new ArrayList<VeritProofSet>(); 

    public VeritProofSet(String name, String type, List<Formula> conclusions,
            List<VeritProofSet> clauses, Integer iargs) {
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

    public List<Formula> getConclusion() {
        return conclusions;
    }

    public List<VeritProofSet> getClauses() {
        return clauses;
    }

    public Integer getIargs() {
        return iargs;
    }
    
    public ImmutableArrayList<VeritProofSet> getParents()
    {
        return new ImmutableArrayList<VeritProofSet>(parents);
    }
    
    public void addParent(VeritProofSet parent)
    {
        parents.add(parent);
    }
    
    public boolean removeParent(VeritProofSet parent)
    {
        return parents.remove(parent);
    }
    
    @Override
    public String toString()
    {
        return "(set "+name+" ("+type+" :..."; // TODO
    }

}
