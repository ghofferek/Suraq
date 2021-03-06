/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.Util;

/**
 * A formula consisting of the equality of domain terms.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class DomainEq extends EqualityFormula {

    /**
     * 
     */
    private static final long serialVersionUID = -8408624046605834100L;

    /**
     * 
     * Constructs a new <code>TermEq</code>.
     * 
     * @param terms
     *            the terms of the (in)equality.
     * @param equal
     *            <code>true</code> if an equality should be constructed,
     *            <code>false</code> for an inequality.
     * 
     */
    private DomainEq(Collection<? extends DomainTerm> domainTerms, boolean equal) {
        super(domainTerms, equal);
    }

    public static DomainEq create(Collection<? extends DomainTerm> domainTerms,
            boolean equal) {
        return (DomainEq) FormulaCache.equalityFormula.put(new DomainEq(
                domainTerms, equal));
    }

    /**
     * Returns a list (copy) of the terms compared by this formula.
     * 
     * @return a list of the terms compared by this formula.
     */
    public List<DomainTerm> getDomainTerms() {
        List<DomainTerm> terms = new ArrayList<DomainTerm>();
        for (Term term : this.terms)
            terms.add(((DomainTerm) term));
        return terms;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        return this; // experimental
        /*
         * List<DomainTerm> terms = new ArrayList<DomainTerm>(); for (Term term
         * : this.terms) { terms.add((DomainTerm) term.deepTermCopy()); } return
         * FormulaCache.equalityFormula.put(new DomainEq(terms, equal));
         */
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> indexSet = new HashSet<DomainTerm>();
        for (Term term : terms)
            indexSet.addAll(((DomainTerm) term).getIndexSet());
        return indexSet;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.EqualityFormula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        List<Term> pairs = new ArrayList<Term>(terms);
        for (DomainTerm term : getDomainTerms()) {
            if (term instanceof ArrayRead) {
                while (pairs.remove(term)) {
                    // this block is intentionally empty
                }
                pairs.add(((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars));
            } else {
                pairs.remove(term);
                pairs.add(term
                        .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars));
            }
        }
        try {
            return EqualityFormula.create(pairs, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.List,
     *      java.util.Map)
     */
    @Override
    public Formula tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding,
            Map<Formula, PropositionalVariable> done, int partition) {

        assert (terms.size() == 2);
        // TODO: split larger equalities

        assert (clauses != null);
        assert (encoding != null);

        // BEGIN OLD CODE
        // Literals should not be Tseitin encoded. This is a waste.

        // Set<Integer> partitions = this.getPartitionsFromSymbols();
        // assert (partitions.size() == 1 || partitions.size() == 2);
        // if (partitions.size() == 2)
        // partitions.remove(-1);
        // assert (partitions.size() == 1);
        // int partition = partitions.iterator().next();
        // PropositionalVariable tseitinVar = Util.freshTseitinVar(partition);
        // encoding.put(tseitinVar, this.deepFormulaCopy());
        //
        // List<Formula> disjuncts = new ArrayList<Formula>(2);
        // disjuncts.add(NotFormula.create(tseitinVar));
        // disjuncts.add(this.deepFormulaCopy());
        // clauses.add(OrFormula.generate(disjuncts));
        //
        // disjuncts.clear();
        // disjuncts.add(tseitinVar);
        // disjuncts.add(NotFormula.create(this.deepFormulaCopy()));
        // clauses.add(OrFormula.generate(disjuncts));
        // return tseitinVar;

        // END OLD CODE - BEGIN REPLACEMENT
        Set<Integer> partitions = this.getPartitionsFromSymbols();
        assert (partitions.size() == 1 || partitions.size() == 2);
        if (partitions.size() == 2)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        assert (partitions.iterator().next().equals(partition) || partitions
                .iterator().next().equals(-1));

        assert (Util.isLiteral(this));
        return this;
        // END REPLACEMENT

    }

    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        List<Term> terms2 = new ArrayList<Term>();

        for (DomainTerm term : getDomainTerms()) {
            if (term instanceof UninterpretedFunctionInstance) {

                DomainVariable auxiliaryVariable = ((UninterpretedFunctionInstance) term)
                        .applyReplaceUninterpretedFunctions(topLeveFormula,
                                functionInstances, instanceParameters,
                                noDependenceVars);
                terms2.add(auxiliaryVariable);

            } else
                terms2.add(term.uninterpretedFunctionsToAuxiliaryVariablesTerm(
                        topLeveFormula, functionInstances, instanceParameters,
                        noDependenceVars));
        }
        try {
            return EqualityFormula.create(terms2, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getLiterals(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getLiterals(Set<Formula> result, Set<Formula> done) {
        if (done.contains(this))
            return;
        assert (terms.size() == 2);
        result.add(this);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#numAigNodes(java.util.Set)
     */
    @Override
    public int numAigNodes(Set<Formula> done) {
        if (done.contains(this))
            return 0;
        assert (terms.size() == 2);
        done.add(this);
        return 0;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toAig(TreeMap, java.util.Map)
     */
    @Override
    public int toAig(TreeMap<Integer, Integer[]> aigNodes,
            Map<Formula, Integer> done) {
        assert (this.terms.size() == 2);
        assert (done.get(this) != null);
        return done.get(this) ^ (equal ? 0 : 1);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getTerms(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getTerms(Set<Term> result, Set<Formula> done) {
        if (done.contains(this))
            return;

        result.addAll(terms);

        done.add(this);
    }
}
