/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.proof;

import java.util.Hashtable;

import at.iaik.suraq.sexp.Token;

public class VeriTToken {
    /**
     * A list of predefined Tokens that are allowed in the VeritProofNode.
     */
    private static final Hashtable<String, Token> tokens = new Hashtable<String, Token>();

    // Here are the predefined Tokens defined, that are allowed in the
    // VeritProofNode.
    public final static Token INPUT = VeriTToken.generate("input");
    public final static Token AND = VeriTToken.generate("and");
    public final static Token OR = VeriTToken.generate("or");
    public final static Token RESOLUTION = VeriTToken.generate("resolution");
    public final static Token EQ_TRANSITIVE = VeriTToken
            .generate("eq_transitive");
    public final static Token EQ_CONGRUENT = VeriTToken
            .generate("eq_congruent");

    public final static Token EQ_CONGRUENT_PRED = VeriTToken
            .generate("eq_congruent_pred");
    public final static Token EQ_REFLEXIVE = VeriTToken
            .generate("eq_reflexive");

    /**
     * returns an existing token with that name or returns a new one.
     * 
     * @param name
     * @return
     */
    private static Token generate(String name) {
        Token token = Token.generate(name);
        tokens.put(name, token);
        return token;
    }

    /**
     * returns an existing Token with that name. If the name does not exist, a
     * new one is generated, but a message is sent to stderr!
     * 
     * @param name
     * @return
     */
    public static Token parse(String name) {
        if (tokens.containsKey(name))
            return tokens.get(name);
        System.err
                .println("The Token '"
                        + name
                        + "' was not found in VeriTToken. You may want to add a field in class at.iaik.suraq.proof.VeriTToken");

        return generate(name);
    }

}
