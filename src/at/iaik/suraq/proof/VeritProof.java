package at.iaik.suraq.proof;

import java.util.HashMap;
import java.util.List;

import at.iaik.suraq.smtlib.formula.Formula;

public class VeritProof {

    protected final HashMap<String, VeritProofSet> proofSets = new HashMap<String, VeritProofSet>();

    public void addProofSet(String name, String type,
            List<Formula> conclusions, List<VeritProofSet> clauses,
            Integer iargs) {
        VeritProofSet tmp = new VeritProofSet(name, type, conclusions, clauses,
                iargs);

        proofSets.put(name, tmp);

        for (VeritProofSet clause : clauses) {
            clause.addParent(tmp);
        }
    }
    

    public VeritProofSet getProofSet(String name) {
        return proofSets.get(name);
    }
    

    @Override
    public String toString()
    {
        return ""; // TODO
    }

}
