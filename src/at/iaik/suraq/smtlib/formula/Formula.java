/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Serializable;
import java.io.Writer;
import java.math.BigInteger;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.HashTagContainer;

/**
 * 
 * This represents formulas in the fragment introduced in the MemoCODE'11 paper.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public interface Formula extends SMTLibObject, Serializable {

    @Override
    public boolean equals(Object formula);

    /**
     * Returns a deep copy of the formula.
     * 
     * @return a deep copy of the formula
     */
    public Formula deepFormulaCopy();

    /**
     * Computes the index set of this formula. (Cf. Bradley/Manna, p. 295) The
     * set does <em>not</em> yet include the new variable <code>lambda</code>.
     * 
     * @return the index set.
     * @throws SuraqException
     *             if the formula contains array write expressions, or
     *             computation otherwise fails.
     */
    public Set<DomainTerm> getIndexSet() throws SuraqException;

    /**
     * Returns a copy of this formula in negation normal form.
     * 
     * @return a copy of this formula in negation normal form.
     * @throws SuraqException
     *             if the formula cannot be converted to NNF, e.g. due to
     *             resulting invalid array properties.
     */
    public Formula negationNormalForm() throws SuraqException;

    /**
     * Returns a new formula that is a version of this formula, with
     * substitutions performed according to the given map. E.g., the local terms
     * of a function macro's body are converted to the (more) global terms of
     * the macro's instance. Terms which are not found in the map are returned
     * unchanged.
     * 
     * @param paramMap
     *            the map to convert local terms to the caller's scope
     * @return a (new) formula, converted according to the given map.
     */
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap,
            Map<SMTLibObject, SMTLibObject> done);

    @Override
    public Formula substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done);

    /**
     * Replaces all array equalities in this formula by equivalent array
     * properties.
     */
    public Formula removeArrayEqualities();

    /**
     * Reduces all array properties in this formula to finite conjunctions over
     * the given index set. The index set must already include the special
     * variable lambda.
     * 
     * @param indexSet
     *            the index set.
     */
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet);

    /**
     * Simplifies this formula by (Boolean) constant propagation and some
     * limited constraint propagation. If the formula cannot be simplified, it
     * is returned unchanged (not copied!). Otherwise a simplified formula is
     * returned. Unchanged subformulas are not copied!
     * 
     * @return this formula, simplified by constant propagation and some
     *         constraint propagation.
     */
    public Formula simplify();

    /**
     * Returns a (new) flattened version of this formula. I.e., macro instances
     * are replaced by their respective instantiations.
     * 
     * @return a flattened copy of this formula.
     */
    public Formula flatten();

    /**
     * Recursively replaces all array writes by applying the write axiom.
     * 
     * @param topLevelFormula
     *            The top-level formula on which the recursion started. (Needed
     *            to determine fresh variable names.)
     * @param constraints
     *            A set to which constraints coming from write-axiom application
     *            will be added.
     * @param noDependenceVars
     *            A set of variables on which the controller may not depend.
     *            Newly created variables on which the controller may not depend
     *            are added to this set during recursion.
     * 
     */
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars);

    /**
     * Replaces all array-read expressions with uninterpreted function instances
     * of the same name.
     * 
     * FIXME: This does not deal with <code>define-fun</code> macros right, if
     * array variables are used as macro parameters. Since uninterpreted
     * functions cannot be used as macro parameters, one would have something
     * more complex, such as making copies of macros.
     * 
     * 
     * @param noDependenceVars
     *            the variables on which the controller may not depend. New such
     *            variables are added to this set during recursion.
     * 
     */
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars);

    /**
     * Replaces all indices of array reads which are not simple domain variables
     * with fresh simple domain variables. Corresponding equality constraints
     * are added to the given set.
     * 
     * @param topLevelFormula
     *            the top level formula (for finding fresh variable names).
     * @param constraints
     *            the set to add new constraints to.
     * @param noDependenceVars
     *            the set of variables on which the controller may not depend.
     *            New variables might be added to this set.
     */
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars);

    /**
     * Creates a copy of this formula in which instances of uninterpreted
     * predicates (functions of return type Bool) are replaced with auxiliary
     * variables and generates corresponding constraints.
     * 
     * @param topLeveFormula
     *            the top level formula (for finding fresh variable names).
     * @param constraints
     *            the set to add new constraints to.
     * @param noDependenceVars
     *            the set of variables on which the controller may not depend.
     *            New variables might be added to this set.
     * @return a new formula with uninterpreted predicates replaced by auxiliary
     *         variables.
     */
    /*
     * public Formula uninterpretedPredicatesToAuxiliaryVariables( Formula
     * topLeveFormula, Set<Formula> constraints, Set<Token> noDependenceVars);
     */

    /**
     * Transforms formulas to consequent formulas. Consequent formulas should
     * have the following structure: - each atom is either a positive equality
     * of two terms, a propositional variable, or an uninterpreted predicate. -
     * each literal is either an atom or a negation of an atom. - formula is
     * always an OR-formula which consists of at least one literal.
     * 
     * @return if transformation is possible, returns formula, otherwise returns
     *         null.
     * 
     */

    public OrFormula transformToConsequentsForm();

    /**
     * Transforms formulas to consequent formulas. Consequent formulas should
     * have the following structure: - each atom is either a positive equality
     * of two terms, a propositional variable, or an uninterpreted predicate. -
     * each literal is either an atom or a negation of an atom. - formula is
     * always an OR-formula which consists of at least one literal.
     * 
     * @param notFlag
     *            indicates that the number of NOT operations occurred so far is
     *            even or odd . (notFlag=true equals an odd number)
     * @param firstLevel
     *            indicates that the function call appeared in the first
     *            recursion step.
     * @return if transformation is possible, returns formula, otherwise returns
     *         null.
     * 
     */
    public Formula transformToConsequentsForm(boolean notFlag,
            boolean firstLevel);

    /**
     * Performs Tseitin encoding to transform a formula into CNF.
     * 
     * @param clauses
     *            a (call-by-reference) parameter to which all the clauses of
     *            the CNF will be added.
     * 
     * @param encoding
     *            a (call-by-reference) parameter, which will contain the
     *            mapping of Tseitin variables to the formulas they represent.
     * @param done
     *            a map of formulas already encoded (to avoid encoding them
     *            again)
     * @param partition
     *            the partition that is encoded (used to assign fresh Tseitin
     *            variables to)
     * @return the Tseitin variable that represents <code>this</code> formula,
     *         or the formula itself if it is a literal/constant.
     */
    public Formula tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding,
            Map<Formula, PropositionalVariable> done, int partition);

    /**
     * Replaces instances of uninterpreted predicates in formula with auxiliary
     * boolean variables.
     * 
     * @param topLeveFormula
     *            the top level formula (for finding fresh variable names).
     * 
     * @param predicateInstances
     *            map containing mapping from predicate names to boolean
     *            auxiliary variables.
     * 
     * @param instanceParameters
     *            map containing mapping from boolean auxiliary variables to
     *            predicate instance parameters.
     * 
     * @return a new formula with uninterpreted predicates replaced by boolean
     *         auxiliary variables.
     */

    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars);

    /**
     * Replaces instances of uninterpreted functions in formula with auxiliary
     * variables.
     * 
     * @param topLeveFormula
     *            the top level formula (for finding fresh variable names).
     * 
     * @param functionInstances
     *            map containing mapping from function names to domain auxiliary
     *            variables.
     * 
     * @param instanceParameters
     *            map containing mapping from domain auxiliary variables to
     *            function instance parameters.
     * 
     * @return a new formula with uninterpreted predicates replaced by auxiliary
     *         domain variables.
     */
    public Formula uninterpretedFunctionsToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars);

    public Formula replaceEquivalences(Formula topLeveFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars);

    public Formula removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList);

    public Formula removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints);

    /**
     * Writes this formula to the given <code>writer</code>, using veriT style
     * hashTags, given via <code>tagContainer</code>. This is used to write
     * veriT-style proofs.
     * 
     * 
     * @param writer
     * @param tagContainer
     * @param handleThisWithTagContainer
     *            whether or not to try to handle <code>this</code> formula via
     *            the <code>tagContainer</code>
     */
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer,
            boolean handleThisWithTagContainer) throws IOException;

    /**
     * Writes this formula to the given writer. This method should write the
     * same thing <code>toString</code> would produce.
     * 
     * @param writer
     * @throws IOException
     */
    public void writeTo(Writer writer) throws IOException;

    /**
     * Writes this formula to the given <code>writer</code>, using the given
     * <code>definitions</code>. The <code>definitions</code> must contain all
     * the formulas and terms that are directly referenced by this formula.
     * 
     * @param writer
     * @param definitions
     * @throws IOException
     */
    public void writeTo(Writer writer, Map<SMTLibObject, String> definitions)
            throws IOException;

    /**
     * Adds all literals of this formula to <code>result</code>. Uses
     * <code>done</code> as a cache to avoid DAG-unrolling.
     * 
     * @param result
     * @param done
     */
    public void getLiterals(Set<Formula> result, Set<Formula> done);

    /**
     * Computes the number of AIG nodes necessary to encode this formula in a
     * DAG-aware way.
     * 
     * @param done
     *            cache to avoid unrolling the DAG.
     * @return the number of AIG nodes
     */
    public int numAigNodes(Set<Formula> done);

    /**
     * Computes AIG nodes corresponding to the formula
     * 
     * @param aigNodes
     *            the definition of the nodes
     * @param done
     *            cache mapping (sub)formulas to AIGER literals (initialize with
     *            ground literals of the formula)
     * @return the AIGER variable representing this formula
     */
    public int toAig(TreeMap<Integer, Integer[]> aigNodes,
            Map<Formula, Integer> done);

    /**
     * Computes the size of this formula (in terms of nodes in the syntax tree),
     * either with or without expansion of the DAG. Both computations are done
     * DAG-aware.
     * 
     * @param expandDAG
     * @param done
     * @return
     */
    public BigInteger size(boolean expandDAG, Map<Formula, BigInteger> done);

    /**
     * Computes the parent-mapping in this formula. I.e., a node maps to a set
     * of its parents.
     * 
     * @param parents
     *            results will be written to this map
     * @param done
     *            used for DAG-awareness.
     */
    public void computeParents(Map<Formula, Set<Formula>> parents,
            Set<Formula> done);

    /**
     * Computes the set of all subformulas which have only "leafs" as their
     * subformulas. "Leafs" are constants, variables, equalities, predicates.
     * 
     * @param onlyLeafChildren
     * @param done
     */
    public void computeSubformulasWithOnlyLeafChildren(
            Set<Formula> onlyLeafChildren, Set<Formula> leaves,
            Set<Formula> done);

    /**
     * 
     * @param formulaSet
     * @return <code>true</code> iff this formula depends only on formulas from
     *         <code>formulaSet</code>.
     */
    public boolean dependsOnlyOn(Set<Formula> formulaSet);

    /**
     * Adds all terms in this formula to the <code>result</code> set. Only adds
     * top-level terms, not their subterms.
     * 
     * @param result
     * @param done
     *            cache to avoid unrolling the DAG.
     */
    public void getTerms(Set<Term> result, Set<Formula> done);

}
