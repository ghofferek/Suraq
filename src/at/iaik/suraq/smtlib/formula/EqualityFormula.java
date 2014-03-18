/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import at.iaik.suraq.exceptions.IncomparableTermsException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.main.GraphReduction;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.HashTagContainer;
import at.iaik.suraq.util.ImmutableArrayList;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class EqualityFormula implements Formula {
    /**
     * 
     */
    private static final long serialVersionUID = -6614135139526500209L;

    /**
     * The terms to be compared.
     */
    protected final ImmutableArrayList<Term> terms;

    /**
     * <code>true</code> for an equality, <code>false</code> for an inequality.
     */
    protected final boolean equal;

    private final int hashCode;

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
        assert (terms != null);
        assert (terms.size() > 1);
        this.equal = equal;
        ArrayList<Term> termList = new ArrayList<Term>(terms);
        // for (Term term : terms)
        // termList.add(term);
        this.terms = new ImmutableArrayList<Term>(termList);
        hashCode = terms.hashCode() * (equal ? 1 : -1);
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
            return DomainEq.create(domainTerms, equal);
        }

        if (termType.equals(Term.arrayTermClass)) {
            Collection<ArrayTerm> arrayTerms = new ArrayList<ArrayTerm>();
            for (Term term : terms) {
                arrayTerms.add((ArrayTerm) term);
            }
            return ArrayEq.create(arrayTerms, equal);
        }

        if (termType.equals(Term.propositionalTermClass)) {
            Collection<PropositionalTerm> propositionalTerms = new ArrayList<PropositionalTerm>();
            for (Term term : terms) {
                propositionalTerms.add((PropositionalTerm) term);
            }
            return PropositionalEq.create(propositionalTerms, equal);
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
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : terms)
            term.getArrayVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getDomainVariables()
     */
    @Override
    public void getDomainVariables(Set<DomainVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : terms)
            term.getDomainVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getPropositionalVariables()
     */
    @Override
    public void getPropositionalVariables(Set<PropositionalVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : terms)
            term.getPropositionalVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
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
        return AndFormula.generate(pairs);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : terms)
            term.getUninterpretedFunctionNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : terms)
            term.getFunctionMacroNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
     */
    @Override
    public void getFunctionMacros(Set<FunctionMacro> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : terms)
            term.getFunctionMacros(result, done);
        done.add(this);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(this.getClass().isInstance(obj)))
            return false;
        if (!((EqualityFormula) obj).terms.equals(terms))
            return false;
        if (((EqualityFormula) obj).equal != equal)
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        return true;
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> indexSet = new HashSet<DomainTerm>();
        for (Term term : terms)
            indexSet.addAll(term.getIndexSet());
        return indexSet;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.containsKey(this)) {
            assert (done.get(this) != null);
            assert (done.get(this) instanceof Formula);
            return (Formula) done.get(this);
        }
        List<Term> convertedTerms = new ArrayList<Term>();
        for (Term term : terms)
            convertedTerms.add(term.substituteTerm(paramMap, done));
        try {
            Formula result = EqualityFormula.create(convertedTerms, equal);
            assert (result != null);
            done.put(this, result);
            return result;
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
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualitiesTerm()
     */
    @Override
    public Formula removeArrayEqualities() {
        // If this equality is an array equality, it will be dealt with on a
        // higher level.
        // For other equalities, recurse on their terms.
        List<Term> pairs = new ArrayList<Term>();
        for (Term term : terms) {
            pairs.add(term.removeArrayEqualitiesTerm());
        }
        try {
            return EqualityFormula.create(pairs, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        // recurse on terms (ITE terms may have formulas in them)
        List<Term> pairs = new ArrayList<Term>();
        for (Term term : terms) {
            pairs.add(term.arrayPropertiesToFiniteConjunctionsTerm(indexSet));
        }
        try {
            return EqualityFormula.create(pairs, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        List<Term> terms = new ArrayList<Term>(this.terms);

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
                return PropositionalConstant.create(true);

        } else {
            if (termSet.size() != terms.size())
                return PropositionalConstant.create(false);
        }

        try {
            return EqualityFormula.create(terms, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
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
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
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
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        List<Term> pairs = new ArrayList<Term>();
        for (Term term : terms)
            pairs.add(term.removeArrayWritesTerm(topLevelFormula, constraints,
                    noDependenceVars));
        try {
            return EqualityFormula.create(pairs, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        List<Term> pairs = new ArrayList<Term>();
        for (Term term : terms)
            pairs.add(term
                    .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars));
        try {
            return EqualityFormula.create(pairs, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : terms)
            term.getUninterpretedFunctions(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Formula substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions) {
        List<Term> pairs = new ArrayList<Term>();
        for (Term term : terms)
            pairs.add(term.substituteUninterpretedFunctionTerm(substitutions));
        try {
            return EqualityFormula.create(pairs, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }

    }

    /**
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.toSmtlibV2().toString();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(Formula,
     *      java.util.Set, Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        List<Term> pairs = new ArrayList<Term>();
        for (Term term : terms)
            pairs.add(term.makeArrayReadsSimpleTerm(topLevelFormula,
                    constraints, noDependenceVars));
        try {
            return EqualityFormula.create(pairs, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = new TreeSet<Integer>();

        for (Term term : terms)
            partitions.addAll(term.getPartitionsFromSymbols());

        return partitions;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm()
     */
    @Override
    public OrFormula transformToConsequentsForm() {
        return (OrFormula) transformToConsequentsForm(false, true);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#transformToConsequentsForm(boolean,
     *      boolean)
     */
    @Override
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel) {

        List<Formula> literals = new ArrayList<Formula>();
        boolean equal = this.equal;

        // TODO: make this.equal final
        if (terms.size() != 2)
            throw new RuntimeException(
                    "Equality should have only two terms for consequents form");

        try {
            if (((equal == true) && (notFlag == false))
                    || ((equal == false) && (notFlag == true))) {
                equal = true;
                if (firstLevel == true) {
                    literals.add(EqualityFormula.create(terms, equal));
                    return OrFormula.generate(literals);
                } else
                    return EqualityFormula.create(terms, equal);

            } else if (((equal == false) && (notFlag == false))
                    || ((equal == true) && (notFlag == true))) {
                equal = true;
                if (firstLevel == true) {
                    literals.add(NotFormula.create(EqualityFormula.create(
                            terms, equal)));
                    return OrFormula.generate(literals);
                } else
                    return NotFormula.create(EqualityFormula.create(terms,
                            equal));
            } else
                throw new RuntimeException("This point should not be reachable");
        } catch (Exception ex) {
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     */
    @Override
    public int compareTo(SMTLibObject o) {
        return this.toString().compareTo(o.toString());
    }

    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        List<Term> pairs = new ArrayList<Term>();
        for (Term term : terms)
            pairs.add(term.uninterpretedPredicatesToAuxiliaryVariablesTerm(
                    topLeveFormula, predicateInstances, instanceParameters,
                    noDependenceVars));
        try {
            return EqualityFormula.create(pairs, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        List<Term> pairs = new ArrayList<Term>();
        for (Term term : terms)
            pairs.add(term.uninterpretedFunctionsToAuxiliaryVariablesTerm(
                    topLeveFormula, functionInstances, instanceParameters,
                    noDependenceVars));
        try {
            return EqualityFormula.create(pairs, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        // FormulaTerm

        // System.out.println("Equivalence found: "+this.numTerms());
        List<Formula> newTerms = new ArrayList<Formula>();
        try {
            // Iterate through all terms of the Equality, because there could be
            // more than two.
            for (int i = 0; i < terms.size(); i++) {
                Term ti = terms.get(i);
                // if(!(ti instanceof PropositionalVariable || ti instanceof
                // FormulaTerm)) // do not handle propositional variables
                for (int j = i + 1; j < terms.size(); j++) {
                    Term tj = terms.get(j);
                    // if(!(tj instanceof PropositionalVariable || tj instanceof
                    // FormulaTerm)) // do not handle propositional variables
                    {
                        // fix to a static order
                        if (ti.toString().compareTo(tj.toString()) > 0) {
                            Term help = tj;
                            tj = ti;
                            ti = help;
                        }

                        // Build EqualityFormula for the Map
                        Collection<Term> terms = new HashSet<Term>();
                        terms.add(ti);
                        terms.add(tj);

                        if (terms.size() < 2) // this means ti = tj
                        {
                            // System.out.println("Propably there was an equality like x=x");
                            newTerms.add(PropositionalConstant.create(true));
                            continue;
                        }

                        EqualityFormula ef = EqualityFormula
                                .create(terms, true);

                        // Find a name for the Equality
                        String newName;
                        if (replacements.containsKey(ef)) {
                            // take an existent replacement because it's the
                            // same
                            newName = replacements.get(ef);
                            // System.err.print('+'); // approx. 44000 times
                        } else {
                            // add a new replacement -> get a new Varname and
                            // add to the list
                            // newName = "eq_"+ti.toString()+"_"+tj.toString();
                            // newName = Util.freshVarNameCached(topLeveFormula,
                            // newName);
                            newName = GraphReduction.getVarName(topLeveFormula,
                                    ti.toString(), tj.toString());
                            replacements.put(ef, newName);
                            if (noDependenceVars.contains(Token.generate(ti
                                    .toString()))
                                    || noDependenceVars.contains(Token
                                            .generate(tj.toString()))) {
                                noDependenceVars.add(Token.generate(newName));
                            }
                        }

                        // we must take care of inequalities, so we add a NOT
                        // around single terms
                        // x != y != z <=> x!=y && x!=z && y!=z <=> e12 && e13
                        // && e23
                        if (this.equal)
                            newTerms.add(PropositionalVariable.create(newName));
                        else
                            newTerms.add(NotFormula
                                    .create(PropositionalVariable
                                            .create(newName)));
                    }
                }
            }

            // Concat the Terms with an AND-Formula, if there are more terms
            // than two. e.g.:
            // x=y <=> e_xy
            // x=y=z <=> e_xy && e_xz && e_yz
            if (newTerms.size() == 0) {
                // This should never happen.
                throw new RuntimeException(
                        "??? Don't know what happened here ???");
            } else if (newTerms.size() == 1) {
                return newTerms.iterator().next();
            } else {
                return AndFormula.generate(newTerms);
            }

        } catch (IncomparableTermsException ex) {
            // This Exception should not be possible.
            // But it is necessary to suppress warnings.
            throw new RuntimeException("Incomparable Terms in Equality Formula");
        }
        // TODO recursively
    }

    @Override
    public Formula removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        /*
         * List<Formula> _andlist = new ArrayList<Formula>();
         * 
         * List<Term> terms2 = new ArrayList<Term>(); for (int i = 0; i <
         * terms.size(); i++) { if (terms.get(i) instanceof DomainIte) {
         * DomainIte domainITE = (DomainIte) terms.get(i);
         * 
         * // replace the ITE with a new variable // the ITE-constraint is added
         * on the end of the topLevelFormula // by this function Holder<Term>
         * newVarName = new Holder<Term>();
         * _andlist.add(domainITE.removeDomainITE(topLevelFormula,
         * noDependenceVars, newVarName, andPreList)); // terms.set(i,
         * newVarName.value); terms2.add(newVarName.value);
         * 
         * // GH 2013-04-30: The following block seems wrong. // It should
         * suffice if the variables *within* the // DomainIte are checked. The
         * variables to which it // is equated should not count! // ---- // if
         * (Util.formulaContainsAny(this, noDependenceVars)) { // assert
         * (newVarName.value instanceof DomainVariable); // Token name = Token
         * // .generate(((DomainVariable) newVarName.value) // .getVarName());
         * // noDependenceVars.add(name); // }
         * 
         * } else terms2.add(terms.get(i).removeDomainITE(topLevelFormula,
         * noDependenceVars, andPreList)); }
         * 
         * andPreList.addAll(_andlist); try { return
         * EqualityFormula.create(terms2, equal); } catch (Exception ex) {
         * ex.printStackTrace(); throw new RuntimeException(ex); }
         */

        List<Term> newTerms = new ArrayList<Term>(terms.size());
        for (Term term : terms) {
            newTerms.add(term.removeDomainITE(topLevelFormula,
                    noDependenceVars, andPreList));
        }
        try {
            return EqualityFormula.create(newTerms, equal);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected exception while removing DomainITEs.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public EqualityFormula uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars) {
        List<Term> newTerms = new ArrayList<Term>(terms.size());
        for (Term term : terms) {
            Term newTerm = term
                    .uninterpretedFunctionsBackToArrayReads(arrayVars);
            newTerms.add(newTerm);
        }
        try {
            return EqualityFormula.create(newTerms, equal);
        } catch (IncomparableTermsException exc) {
            throw new RuntimeException(
                    "Unexpected IncomparableTermsException while back-substituting array reads.",
                    exc);
        }
    }

    @Override
    public EqualityFormula removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {

        List<Term> newTerms = new ArrayList<Term>(terms.size());
        for (Term term : terms) {
            newTerms.add(term.removeArrayITE(topLevelFormula, noDependenceVars,
                    constraints));
        }
        try {
            return EqualityFormula.create(newTerms, equal);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected exception while removing ArrayITEs.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeOut(java.io.BufferedWriter,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer,
            boolean handleThisWithTagContainer) throws IOException {

        if (handleThisWithTagContainer) {
            tagContainer.handle(this, writer);
        } else {
            writer.append('(')
                    .append(this.equal ? SExpressionConstants.EQUAL.toString()
                            : SExpressionConstants.DISTINCT.toString())
                    .append(' ');
            for (Term term : terms) {
                term.writeOut(writer, tagContainer);
                writer.append(' ');
            }
            writer.append(") ");
        }

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.append('(')
                .append(this.equal ? SExpressionConstants.EQUAL.toString()
                        : SExpressionConstants.DISTINCT.toString()).append(' ');
        for (Term term : terms) {
            term.writeTo(writer);
            writer.append(' ');
        }
        writer.append(") ");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#size(boolean, java.util.Map)
     */
    @Override
    public long size(boolean expandDAG, Map<Formula, Long> done) {
        if (done.get(this) != null) {
            if (expandDAG)
                return done.get(this);
            else
                return 0;
        }

        assert (terms.size() == 2);
        long result = 1;
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#computeParents(java.util.Map,
     *      java.util.Set)
     */
    @Override
    public void computeParents(Map<Formula, Set<Formula>> parents,
            Set<Formula> done) {
        return; // Leaf node
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#computeSubformulasWithOnlyLeafChildren(java.util.Set,
     *      java.util.HashSet)
     */
    @Override
    public void computeSubformulasWithOnlyLeafChildren(
            Set<Formula> onlyLeafChildren, Set<Formula> leaves,
            Set<Formula> done) {
        if (done.contains(this))
            return;
        if (leaves.contains(this)) {
            done.add(this);
            return;
        }

        done.add(this);
        return;
    }
}
