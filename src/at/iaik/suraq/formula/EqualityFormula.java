/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class EqualityFormula implements Formula {
    /**
     * The terms to be compared.
     */
    protected final List<Term> terms;

    /**
     * <code>true</code> for an equality, <code>false</code> for an inequality.
     */
    protected final boolean equal;

    /**
     * 
     * Constructs a new <code>EqualityFormula</code>.
     * 
     * @param terms
     *            the list of terms
     * @param equal
     *            <code>true</code> if it is an equality, <code>false</code> if
     *            it is an inequality.
     */
    protected EqualityFormula(Collection<? extends Term> terms, boolean equal) {
        this.equal = equal;
        ArrayList<Term> termList = new ArrayList<Term>();
        for (Term term : terms)
            termList.add(term);
        this.terms = termList;
    }

    /**
     * Creates an instance of (an adequate subclass of)
     * <code>EqualityFormula</code>, based on the given <code>terms</code>.
     * 
     * @param terms
     *            the list of terms to compare.
     * @param equal
     *            <code>true</code> if it is an equality, <code>false</code> if
     *            it is an inequality.
     * @return an instance of the adequate subclass of
     *         <code>EqualityFormula</code>.
     * @throws IncomparableTermsException
     *             if the given terms are incomparable.
     */
    public static EqualityFormula create(Collection<? extends Term> terms,
            boolean equal) throws IncomparableTermsException {

        Class<?> termType = Term.checkTypeCompatibility(terms);
        if (termType == null)
            throw new IncomparableTermsException();

        if (termType.equals(Term.domainTermClass)) {
            Collection<DomainTerm> domainTerms = new ArrayList<DomainTerm>();
            for (Term term : terms) {
                domainTerms.add((DomainTerm) term);
            }
            return new DomainEq(domainTerms, equal);
        }

        if (termType.equals(Term.arrayTermClass)) {
            Collection<ArrayTerm> arrayTerms = new ArrayList<ArrayTerm>();
            for (Term term : terms) {
                arrayTerms.add((ArrayTerm) term);
            }
            return new ArrayEq(arrayTerms, equal);
        }

        if (termType.equals(Term.propositionalTermClass)) {
            Collection<PropositionalTerm> propositionalTerms = new ArrayList<PropositionalTerm>();
            for (Term term : terms) {
                propositionalTerms.add((PropositionalTerm) term);
            }
            return new PropositionalEq(propositionalTerms, equal);
        }

        // This should never be reached
        throw new RuntimeException(
                "Unexpected situation while trying to construct term equality.");
    }

    /**
     * Returns a list (copy) of the terms compared by this formula.
     * 
     * @return a list of the terms compared by this formula.
     */
    public List<Term> getTerms() {
        return new ArrayList<Term>(terms);
    }

    /**
     * Determines whether this is an equality or an inequality.
     * 
     * @return <code>true</code> if this is an equality, <code>false</code>
     *         otherwise.
     */
    public boolean isEqual() {
        return equal;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Term term : terms)
            variables.addAll(term.getArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Term term : terms)
            variables.addAll(term.getDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Term term : terms)
            variables.addAll(term.getPropositionalVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {

        return this.deepFormulaCopy();
    }

    /**
     * @return
     */
    public boolean isPair() {
        return terms.size() == 2;
    }

    /**
     * @return
     */
    public AndFormula toPairwise() {
        List<Formula> pairs = new ArrayList<Formula>();
        for (int i = 0; i < terms.size(); i++) {
            for (int j = i; j < terms.size(); j++) {
                List<Term> list = new ArrayList<Term>();
                list.add(terms.get(i));
                list.add(terms.get(j));
                try {
                    pairs.add(EqualityFormula.create(list, equal));
                } catch (IncomparableTermsException exc) {
                    // This should never happen
                    throw new RuntimeException(
                            "Unexpected situaton while making pairwise equalities.",
                            exc);
                }
            }
        }
        return new AndFormula(pairs);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> functionNames = new HashSet<String>();
        for (Term term : terms)
            functionNames.addAll(term.getUninterpretedFunctionNames());
        return functionNames;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> macroNames = new HashSet<String>();
        for (Term term : terms)
            macroNames.addAll(term.getFunctionMacroNames());
        return macroNames;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
        for (Term term : terms)
            macros.addAll(term.getFunctionMacros());
        return macros;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (!(this.getClass().isInstance(obj)))
            return false;
        if (!((EqualityFormula) obj).terms.equals(terms))
            return false;
        if (((EqualityFormula) obj).equal != equal)
            return false;
        return true;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return terms.hashCode() + (equal ? 1 : 0);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> indexSet = new HashSet<DomainTerm>();
        for (Term term : terms)
            indexSet.addAll(term.getIndexSet());
        return indexSet;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#substituteFormula(java.util.Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, Term> paramMap) {
        List<Term> convertedTerms = new ArrayList<Term>();
        for (Term term : terms)
            convertedTerms.add(term.substituteTerm(paramMap));
        try {
            return EqualityFormula.create(convertedTerms, equal);
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Unexpected problems with term types while converting EqualityFormula to caller scope.",
                    exc);
        }
    }

    /**
     * Returns the number of terms compared by this equality.
     * 
     * @return the number of terms compared by this equality.
     */
    public int numTerms() {
        return terms.size();
    }

    /**
     * @see at.iaik.suraq.formula.Formula#removeArrayEqualities()
     */
    @Override
    public void removeArrayEqualities() {
        // If this equality is an array equality, it will be dealt with on a
        // higher level.
        // For other equalities, recurse on their terms.
        for (Term term : terms) {
            term.removeArrayEqualities();
        }
        return;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public void arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        // recurse on terms (ITE terms may have formulas in them)
        for (Term term : terms) {
            term.arrayPropertiesToFiniteConjunctions(indexSet);
        }
        return;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {

        for (int count = 0; count < terms.size(); count++) {
            if (terms.get(count) instanceof DomainIte)
                terms.set(count, ((DomainIte) terms.get(count)).simplify());

            if (terms.get(count) instanceof ArrayIte)
                terms.set(count, ((ArrayIte) terms.get(count)).simplify());
        }

        Set<Term> termSet = new HashSet<Term>(terms);

        if (equal) {
            terms.clear();
            terms.addAll(termSet);

            if (terms.size() < 2)
                return new PropositionalConstant(true);

        } else {
            if (termSet.size() != terms.size())
                return new PropositionalConstant(false);
        }

        return this;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        List<Term> termCopies = new ArrayList<Term>();

        for (Term term : terms)
            termCopies.add(term.flatten());

        try {
            return EqualityFormula.create(termCopies, equal);
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Unforeseen exception while flattening equality formula.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> expr = new ArrayList<SExpression>();
        expr.add(equal ? SExpressionConstants.EQUAL
                : SExpressionConstants.DISTINCT);
        for (Term term : terms)
            expr.add(term.toSmtlibV2());
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#removeArrayWrites(at.iaik.suraq.formula.Formula)
     */
    @Override
    public void removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        for (Term term : terms)
            term.removeArrayWrites(topLevelFormula, constraints,
                    noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public void arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        for (Term term : terms)
            term.arrayReadsToUninterpretedFunctions(noDependenceVars);
    }

    /**
     * @see at.iaik.suraq.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> functions = new HashSet<UninterpretedFunction>();
        for (Term term : terms)
            functions.addAll(term.getUninterpretedFunctions());
        return functions;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.formula.UninterpretedFunction)
     */
    @Override
    public void substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        for (Term term : terms)
            term.substituteUninterpretedFunction(oldFunction, newFunction);

    }

    /**
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.toSmtlibV2().toString();
    }
}
