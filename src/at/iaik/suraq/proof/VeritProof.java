package at.iaik.suraq.proof;

import java.util.HashMap;
import java.util.List;

import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.util.ImmutableHashSet;

@SuppressWarnings("deprecation")
public class VeritProof {

    protected final HashMap<String, VeritProofSet> proofSets = new HashMap<String, VeritProofSet>();

    public VeritProofSet addProofSet(String name, String type,
            List<Formula> conclusions, List<VeritProofSet> clauses,
            Integer iargs) {
        VeritProofSet tmp = new VeritProofSet(name, type, conclusions, clauses,
                iargs);

        proofSets.put(name, tmp);

        if (clauses != null) {
            for (VeritProofSet clause : clauses) {
                clause.addParent(tmp);
            }
        }
        return tmp;
    }

    public void removeProofSet(VeritProofSet proofSet) {
        for (VeritProofSet clauses : proofSet.getParents())
            clauses.removeClause(proofSet);
        for (VeritProofSet clauses : proofSet.getClauses())
            clauses.removeParent(proofSet);
    }

    public VeritProofSet getProofSet(String name) {
        return proofSets.get(name);
    }

    public ImmutableHashSet<VeritProofSet> getProofIterator() {
        return new ImmutableHashSet<VeritProofSet>(proofSets.values());
    }

    @Override
    public String toString() {
        StringBuilder str = new StringBuilder();
        for (VeritProofSet proof : getProofIterator())
            str = str.append(proof.toString() + "\n");
        return str.toString();
    }

}
