package at.iaik.suraq.proof;

import java.util.Hashtable;

import at.iaik.suraq.sexp.Token;

public class VeriTToken {
    private static final Hashtable<String, Token> tokens = new Hashtable<String, Token>();


    public final static Token INPUT = VeriTToken.generate("input");
    public final static Token AND = VeriTToken.generate("and");
    public final static Token OR = VeriTToken.generate("or");
    public final static Token RESOLUTION = VeriTToken.generate("resolution");
    public final static Token EQ_TRANSITIVE = VeriTToken
            .generate("eq_transitive");
    public final static Token EQ_CONGRUENT = VeriTToken
            .generate("eq_congruent");
    
    
    private static Token generate(String name) {
        Token token = Token.generate(name);
        tokens.put(name, token);
        return token;
    }

    public static Token parse(String name) {
        if (tokens.containsKey(name))
            return tokens.get(name);
        System.err.println("The Token '" + name
                + "' was not found in VeriTToken.");
        throw new RuntimeException("VeriTToken '" + name
                + "' was not defined in VeriTToken.");
    }

}
