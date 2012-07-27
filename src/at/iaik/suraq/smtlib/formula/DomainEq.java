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

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.Token;
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
    public DomainEq(Collection<? extends DomainTerm> domainTerms, boolean equal) {
        super(domainTerms, equal);
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
        List<DomainTerm> terms = new ArrayList<DomainTerm>();
        for (Term term : this.terms) {
            terms.add((DomainTerm) term.deepTermCopy());
        }
        return new DomainEq(terms, equal);
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
            return create(pairs, equal);
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
    public PropositionalVariable tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding) {

        assert (terms.size() == 2);
        // TODO: split larger equalities

        assert (clauses != null);
        assert (encoding != null);

        Set<Integer> partitions = this.getPartitionsFromSymbols();
        assert (partitions.size() == 1 || partitions.size() == 2);
        if (partitions.size() == 2)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        int partition = partitions.iterator().next();
        PropositionalVariable tseitinVar = Util.freshTseitinVar(partition);
        encoding.put(tseitinVar, this.deepFormulaCopy());

        List<Formula> disjuncts = new ArrayList<Formula>(2);
        disjuncts.add(new NotFormula(tseitinVar));
        disjuncts.add(this.deepFormulaCopy());
        clauses.add(OrFormula.generate(disjuncts));

        disjuncts.clear();
        disjuncts.add(tseitinVar);
        disjuncts.add(new NotFormula(this.deepFormulaCopy()));
        clauses.add(OrFormula.generate(disjuncts));

        return tseitinVar;

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

        List<Term> terms2 = new ArrayList<Term>(terms);

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
            return DomainEq.create(terms, equal);
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException(ex);
        }
    }

}
