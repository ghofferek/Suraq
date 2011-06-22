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
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class EqualityFormula implements Formula {
    /**
     * The terms to be compared.
     */
    protected final List<? extends Term> terms;

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
        return new HashSet<DomainTerm>();
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
        // Nothing to do.
        // If this equality is an array equality, it will be dealt with on a
        // higher level.
        // Other equalities do not need transformation.
        return;
    }
}
