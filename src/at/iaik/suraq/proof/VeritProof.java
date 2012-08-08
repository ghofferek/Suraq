package at.iaik.suraq.proof;

import java.util.HashMap;
import java.util.List;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.util.ImmutableHashSet;

@SuppressWarnings("deprecation")
public class VeritProof {

    protected final HashMap<String, VeritProofNode> proofSets = new HashMap<String, VeritProofNode>();

    public VeritProofNode addProofSet(String name, Token type,
            List<Formula> conclusions, List<VeritProofNode> clauses,
            Integer iargs) {
        VeritProofNode tmp = new VeritProofNode(name, type, conclusions, clauses,
                iargs);

        proofSets.put(name, tmp);

        if (clauses != null) {
            for (VeritProofNode clause : clauses) {
                clause.addParent(tmp);
            }
        }
        return tmp;
    }

    public void removeProofSet(VeritProofNode proofNode) {
        for (VeritProofNode parent : proofNode.getParents())
            parent.removeSubProof(proofNode);
        for (VeritProofNode subproof : proofNode.getSubProofs())
            subproof.removeParent(proofNode);
    }

    public VeritProofNode getProofNodes(String name) {
        return proofSets.get(name);
    }

    public ImmutableHashSet<VeritProofNode> getProofIterator() {
        return new ImmutableHashSet<VeritProofNode>(proofSets.values());
    }

    @Override
    public String toString() {
        StringBuilder str = new StringBuilder();
        for (VeritProofNode proof : getProofIterator())
            str = str.append(proof.toString() + "\n");
        return str.toString();
    }

}
