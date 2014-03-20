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
import java.util.TreeMap;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.exceptions.WrongFunctionTypeException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.HashTagContainer;
import at.iaik.suraq.util.ImmutableArrayList;
import at.iaik.suraq.util.Util;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class UninterpretedPredicateInstance extends PropositionalTerm {

    /**
     * 
     */
    private static final long serialVersionUID = 7300557099748461681L;

    private final int hashCode;

    /**
     * The function of which this is an instance.
     */
    private final UninterpretedFunction function;

    /**
     * The list of parameters of this instance.
     */
    private final ImmutableArrayList<DomainTerm> parameters;

    private UninterpretedPredicateInstance(UninterpretedFunction function,
            List<DomainTerm> parameters, int partition)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        this(function, parameters);
        if (partition != -1) {
            assert (partition == this.assertPartition || this.assertPartition == -1);
            this.assertPartition = partition;
        }
    }

    public static UninterpretedPredicateInstance create(
            UninterpretedFunction function, List<DomainTerm> parameters,
            int partition) throws WrongNumberOfParametersException,
            WrongFunctionTypeException {
        return (UninterpretedPredicateInstance) FormulaCache.term
                .put(new UninterpretedPredicateInstance(function, parameters,
                        partition));
    }

    /**
     * Constructs a new <code>UninterpretedPredicateInstance</code> with the
     * given values.
     * 
     * @param function
     *            the function that is applied.
     * @param parameters
     *            the parameters of the function
     * 
     * @throws WrongNumberOfParametersException
     *             if the number of parameters of the function does not match
     *             the size of <code>parameters</code>.
     * @throws WrongFunctionTypeException
     *             if the type of the given function is not <code>Value</code>.
     */
    private UninterpretedPredicateInstance(UninterpretedFunction function,
            List<DomainTerm> parameters)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        if (function.getNumParams() != parameters.size())
            throw new WrongNumberOfParametersException();
        this.function = function;
        if (!function.getType().equals(SExpressionConstants.BOOL_TYPE))
            throw new WrongFunctionTypeException(
                    "Expected a domain function. Received type: "
                            + function.getType().toString());
        this.parameters = new ImmutableArrayList<DomainTerm>(parameters);

        Set<Integer> partitions = new HashSet<Integer>();
        for (DomainTerm parameter : this.parameters)
            partitions.addAll(parameter.getPartitionsFromSymbols());
        assert (partitions.size() <= 2);
        if (partitions.size() == 2)
            partitions.remove(-1);
        assert (partitions.size() == 1);
        this.assertPartition = partitions.iterator().next();
        this.hashCode = this.function.hashCode() * 31
                + this.parameters.hashCode();
    }

    public static UninterpretedPredicateInstance create(
            UninterpretedFunction function, List<DomainTerm> parameters)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        return (UninterpretedPredicateInstance) FormulaCache.term
                .put(new UninterpretedPredicateInstance(function, parameters));
    }

    public static UninterpretedPredicateInstance create(
            UninterpretedFunction function, DomainTerm parameter)
            throws WrongNumberOfParametersException, WrongFunctionTypeException {
        if (function.getNumParams() != 1)
            throw new WrongNumberOfParametersException("Predicate "
                    + function.getName().toString() + " expects "
                    + function.getNumParams() + " parameters.");
        List<DomainTerm> parameters = new ArrayList<DomainTerm>(1);
        parameters.add(parameter);
        return (UninterpretedPredicateInstance) FormulaCache.term
                .put(new UninterpretedPredicateInstance(function, parameters));
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof UninterpretedPredicateInstance))
            return false;
        if (this.hashCode() != obj.hashCode())
            return false;
        UninterpretedPredicateInstance other = (UninterpretedPredicateInstance) obj;
        if (!other.parameters.equals(parameters))
            return false;
        if (!other.function.equals(function))
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
     * Returns the function of which this is an instance
     * 
     * @return the <code>function</code>
     */
    public UninterpretedFunction getFunction() {
        return function;
    }

    /**
     * Returns a copy of the list of parameters of this instance.
     * 
     * @return the <code>parameters</code> (copy)
     */
    public List<DomainTerm> getParameters() {
        return new ArrayList<DomainTerm>(parameters);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public UninterpretedPredicateInstance deepFormulaCopy() {
        return this; // experimental
        /*
         * List<DomainTerm> parameterCopies = new ArrayList<DomainTerm>(); for
         * (DomainTerm term : parameters)
         * parameterCopies.add(term.deepTermCopy()); try { return new
         * UninterpretedPredicateInstance( new UninterpretedFunction(function),
         * parameterCopies, assertPartition); } catch (SuraqException exc) {
         * throw new RuntimeException(
         * "Unexpected situation whily copying predicate.", exc); }
         */
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        for (Term term : parameters)
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
        for (Term term : parameters)
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
        for (Term term : parameters)
            term.getPropositionalVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        result.add(this.function.getName().toString());
        for (DomainTerm term : parameters)
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
        for (Term term : parameters)
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
        for (Term term : parameters)
            term.getFunctionMacros(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        for (DomainTerm term : parameters) {
            result.addAll(term.getIndexSet());
        }
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        return deepFormulaCopy();
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
        List<DomainTerm> convertedParameters = new ArrayList<DomainTerm>();
        for (int count = 0; count < parameters.size(); count++)
            convertedParameters.add((DomainTerm) parameters.get(count)
                    .substituteTerm(paramMap, done));

        UninterpretedPredicateInstance result;
        try {
            result = UninterpretedPredicateInstance.create(function,
                    convertedParameters);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected error while subsituting parameters.", exc);
        }
        assert (result != null);
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(at.iaik.suraq.sexp.Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public UninterpretedPredicateInstance substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null) {
            assert (done.get(this) instanceof UninterpretedPredicateInstance);
            return (UninterpretedPredicateInstance) done.get(this);
        }
        UninterpretedFunction function = this.function;

        if (substitutions.containsKey(function.getName())) {
            function = substitutions.get(function.getName());
            assert ((function.getType()).equals(SExpressionConstants.BOOL_TYPE));
        }
        // if (function.getName().equals(oldFunction)) {
        // function = newFunction;
        // assert (newFunction.getType()
        // .equals(SExpressionConstants.BOOL_TYPE));
        // }

        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term term : parameters)
            paramNew.add((DomainTerm) term.substituteUninterpretedFunction(
                    substitutions, done));

        try {
            UninterpretedPredicateInstance result = UninterpretedPredicateInstance
                    .create(function, paramNew);
            done.put(this, result);
            return result;
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualities()
     */
    @Override
    public Formula removeArrayEqualities() {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param.removeArrayEqualitiesTerm());

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    @Override
    public Term removeArrayEqualitiesTerm() {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param.removeArrayEqualitiesTerm());

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param
                    .arrayPropertiesToFiniteConjunctionsTerm(indexSet));

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    @Override
    public Term arrayPropertiesToFiniteConjunctionsTerm(Set<DomainTerm> indexSet) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param
                    .arrayPropertiesToFiniteConjunctionsTerm(indexSet));

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        return deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public UninterpretedPredicateInstance flatten() {
        List<DomainTerm> flattenedParams = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            flattenedParams.add((DomainTerm) term.flatten());
        try {
            return UninterpretedPredicateInstance.create(function,
                    flattenedParams);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected error while flattening UninterpretedFunctionInstance.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> expr = new ArrayList<SExpression>();
        expr.add(function.getName());
        for (DomainTerm term : parameters)
            expr.add(term.toSmtlibV2());
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param.removeArrayWritesTerm(
                    topLevelFormula, constraints, noDependenceVars));

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param.removeArrayWritesTerm(
                    topLevelFormula, constraints, noDependenceVars));

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions(java.util.Set)
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(
            Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            if (term instanceof ArrayRead) {
                paramNew.add(((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars));
            } else
                paramNew.add((DomainTerm) term
                        .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars));

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(
            Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (DomainTerm term : parameters)
            if (term instanceof ArrayRead) {
                paramNew.add(((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars));
            } else
                paramNew.add((DomainTerm) term
                        .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars));

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    public static boolean method = true; // TODO remove this

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        result.add(function);
        for (DomainTerm term : parameters)
            term.getUninterpretedFunctions(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Formula makeArrayReadsSimple(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {

        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param.makeArrayReadsSimpleTerm(
                    topLevelFormula, constraints, noDependenceVars));

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {

        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();
        for (Term param : parameters)
            paramNew.add((DomainTerm) param.makeArrayReadsSimpleTerm(
                    topLevelFormula, constraints, noDependenceVars));

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public PropositionalTerm
     * uninterpretedPredicatesToAuxiliaryVariables( Formula topLeveFormula,
     * Set<Formula> constraints, Set<Token> noDependenceVars) {
     * PropositionalVariable newVar = new PropositionalVariable(
     * Util.freshVarName(topLeveFormula, "aux")); List<PropositionalTerm> terms
     * = new ArrayList<PropositionalTerm>(); terms.add(newVar);
     * terms.add(FormulaTerm.create(this.deepFormulaCopy()));
     * constraints.add(new PropositionalEq(terms, true));
     * 
     * if (Util.formulaContainsAny(this, noDependenceVars))
     * noDependenceVars.add(new Token(newVar.getVarName()));
     * 
     * return newVar; }
     */

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = function.getAssertPartitionFromSymbols();

        for (DomainTerm term : parameters)
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

        if (firstLevel == true) {
            List<Formula> literals = new ArrayList<Formula>();
            literals.add(this);
            return OrFormula.generate(literals);
        }
        if (notFlag == true)
            return NotFormula.create(this);

        return this;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return deepFormulaCopy();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap,
            Map<SMTLibObject, SMTLibObject> done) {
        return (Term) substituteFormula(paramMap, done);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#tseitinEncode(java.util.List,
     *      java.util.Map)
     */
    @Override
    public Formula tseitinEncode(List<OrFormula> clauses,
            Map<PropositionalVariable, Formula> encoding,
            Map<Formula, PropositionalVariable> done, int partition) {

        // OLD Code (that encodes a predicate instance)
        // assert (clauses != null);
        // assert (encoding != null);
        //
        // Set<Integer> partitions = this.getPartitionsFromSymbols();
        // assert (partitions.size() == 1 || partitions.size() == 2);
        // if (partitions.size() == 2)
        // partitions.remove(-1);
        // assert (partitions.size() == 1);
        // assert (partitions.iterator().next().equals(partition) || partitions
        // .iterator().next().equals(-1));
        //
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

        // BEGIN REPLACEMENT (do not encode predicate instance, as it already is
        // a literal)
        return this;
        // END REPLACEMENT

    }

    /**
     * Searches predicate-instance and instance-parameter mappings for match of
     * current UninterpretedPredicateInstance's function and parameter
     * valuation.
     * 
     * @param predicateInstances
     *            map containing mapping from function names to auxiliary
     *            variables.
     * 
     * @param instanceParameters
     *            map containing mapping from auxiliary variables to function
     *            instance parameters.
     * 
     * @return the found auxiliary PropositionalVariable. If no match exists
     *         NULL is returned.
     */
    private PropositionalVariable matchPredicateInstance(
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters) {

        String predicateName = function.getName().toString();
        List<PropositionalVariable> instances = predicateInstances
                .get(predicateName);

        if (instances != null)
            for (PropositionalVariable instance : instances) {
                List<DomainTerm> instParameters = instanceParameters
                        .get(instance);

                boolean found = true;

                for (int x = 0; x < instParameters.size(); x++) {
                    DomainTerm a = parameters.get(x);
                    DomainTerm b = instParameters.get(x);

                    if (!(a.equals(b))) {
                        found = false;
                        break;
                    }
                }

                if (found)
                    return instance;
            }

        return null;
    }

    /**
     * Add the current UninterpretedPredicateInstance as new entry into the
     * predicate-instance and instance-parameter mappings.
     * 
     * @param predicateInstances
     *            map containing mapping from function names to auxiliary
     *            variables.
     * 
     * @param instanceParameters
     *            map containing mapping from auxiliary variables to function
     *            instance parameters.
     * 
     * @return newly created auxiliary DomainVariable as substitute for the
     *         current UninterpretedFunctionInstace.
     */
    private PropositionalVariable addPredicateInstance(Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters) {

        PropositionalVariable result = null;

        Set<String> instancesStr = new HashSet<String>();
        for (PropositionalVariable pv : instanceParameters.keySet())
            instancesStr.add(pv.getVarName());

        String varName = Util.freshVarNameCached(topLeveFormula, function
                .getName().toString(), instancesStr);

        result = PropositionalVariable.create(varName);

        String predicateName = function.getName().toString();
        List<PropositionalVariable> instances = predicateInstances
                .get(predicateName);
        if (instances == null)
            instances = new ArrayList<PropositionalVariable>();
        instances.add(result);
        predicateInstances.put(predicateName, instances);

        instanceParameters.put(result, parameters);

        return result;
    }

    /**
     * @see at.iaik.suraq.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        throw new RuntimeException(
                "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an UninterpretedPredicateInstance.\nUse applyReplaceUninterpretedPredicates instead.");
    }

    @Override
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        throw new RuntimeException(
                "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an UninterpretedPredicateInstance.\nUse applyReplaceUninterpretedPredicates instead.");
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
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();

        for (DomainTerm term : parameters) {
            if (term instanceof UninterpretedFunctionInstance) {
                DomainVariable auxiliaryVariable = ((UninterpretedFunctionInstance) term)
                        .applyReplaceUninterpretedFunctions(topLeveFormula,
                                functionInstances, instanceParameters,
                                noDependenceVars);

                // chillebold: imho: the order of these terms may be important!
                // parameters.remove(term);
                // parameters.add(auxiliaryVariable);

                // verify if still working - need a testcase for this
                // Let's try this instead.
                // I don't know how the for-loop is implemented.
                // In some programming languages the following action throws an
                // exception, because the for-loop does not know how to
                // continue.
                // parameters.set(parameters.indexOf(term), auxiliaryVariable);
                paramNew.add(auxiliaryVariable);

            } else
                paramNew.add((DomainTerm) term
                        .uninterpretedFunctionsToAuxiliaryVariablesTerm(
                                topLeveFormula, functionInstances,
                                instanceParameters, noDependenceVars));
        }

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            System.err.println("is: " + function.getNumParams() + " should:"
                    + paramNew.size());
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        List<DomainTerm> paramNew = new ArrayList<DomainTerm>();

        for (DomainTerm term : parameters) {
            if (term instanceof UninterpretedFunctionInstance) {
                DomainVariable auxiliaryVariable = ((UninterpretedFunctionInstance) term)
                        .applyReplaceUninterpretedFunctions(topLeveFormula,
                                functionInstances, instanceParameters,
                                noDependenceVars);

                // chillebold: imho: the order of these terms may be important!
                // parameters.remove(term);
                // parameters.add(auxiliaryVariable);

                // verify if still working - need a testcase for this
                // Let's try this instead.
                // I don't know how the for-loop is implemented.
                // In some programming languages the following action throws an
                // exception, because the for-loop does not know how to
                // continue.
                // parameters.set(parameters.indexOf(term), auxiliaryVariable);
                paramNew.add(auxiliaryVariable);

            } else
                term.uninterpretedFunctionsToAuxiliaryVariablesTerm(
                        topLeveFormula, functionInstances, instanceParameters,
                        noDependenceVars);
        }

        try {
            return UninterpretedPredicateInstance.create(function, paramNew);
        } catch (SuraqException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    /**
     * Performs a substitution of UninterpretedPredicateInstances with auxiliary
     * PropositionalVariables.
     * 
     * @param topLeveFormula
     *            the top level formula (for finding fresh variable names).
     * 
     * @param predicateInstances
     *            map containing mapping from predicate names to auxiliary
     *            variables.
     * 
     * @param instanceParameters
     *            map containing mapping from auxiliary variables to function
     *            instance parameters.
     * 
     * @return auxiliary PropositionalVariable as substitute for the current
     *         UninterpretedPredicateInstace.
     */
    public PropositionalVariable applyReplaceUninterpretedPredicates(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        PropositionalVariable result = matchPredicateInstance(
                predicateInstances, instanceParameters);

        if (result == null)
            result = addPredicateInstance(topLeveFormula, predicateInstances,
                    instanceParameters);

        // Check if the function is noDependence or at least one parameter of
        // the function is noDependence
        // This might be conservative and might not be complete (i.e., may
        // result unnecessary unrealizability)

        boolean insert = false;
        for (DomainTerm term : parameters) {
            if (Util.termContainsAny(term, noDependenceVars))
                insert = true;
        }

        String funcName = function.getName().toString();
        for (Token t : noDependenceVars) {
            if (funcName.equals(t.toString())) {
                insert = true;
                break;
            }
        }

        if (insert == true) {
            noDependenceVars.add(Token.generate(result.getVarName()));
        }
        return result;
    }

    @Override
    public Formula replaceEquivalences(Formula topLeveFormula,
            Map<EqualityFormula, String> replacements,
            Set<Token> noDependenceVars) {
        throw new RuntimeException(
                "replaceEquivalences cannot be called on an UninterpretedFunctions.\n"
                        + "UninterpretedFunctions should be removed by now.");
    }

    @Override
    public PropositionalTerm removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        // List<Formula> _andlist = new ArrayList<Formula>();
        // List<DomainTerm> terms2 = new ArrayList<DomainTerm>();
        // for (DomainTerm term : parameters) {
        // if (term instanceof DomainIte) {
        // Holder<Term> newVarName = new Holder<Term>();
        // _andlist.add(((DomainIte) term).removeDomainITE(
        // topLevelFormula, noDependenceVars, newVarName,
        // andPreList));
        // if (Util.formulaContainsAny(this, noDependenceVars)) {
        // assert (newVarName.value instanceof DomainVariable);
        // Token name = Token
        // .generate(((DomainVariable) newVarName.value)
        // .getVarName());
        // noDependenceVars.add(name);
        // }
        // assert (newVarName.value instanceof DomainTerm);
        // terms2.add((DomainTerm) newVarName.value);
        // } else {
        // terms2.add(term.removeDomainITE(topLevelFormula,
        // noDependenceVars, andPreList));
        // }
        // }
        //
        // andPreList.addAll(_andlist);
        // try {
        // return UninterpretedPredicateInstance.create(this.function, terms2);
        // } catch (Exception ex) {
        // ex.printStackTrace();
        // throw new RuntimeException(ex);
        // }

        List<DomainTerm> newParams = new ArrayList<DomainTerm>(
                parameters.size());
        for (DomainTerm parameter : parameters) {
            newParams.add(parameter.removeDomainITE(topLevelFormula,
                    noDependenceVars, andPreList));
        }
        try {
            return UninterpretedPredicateInstance.create(function, newParams);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected exception while removing DomainITEs.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.PropositionalTerm#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public PropositionalTerm uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars) {
        List<DomainTerm> newParameters = new ArrayList<DomainTerm>();
        for (DomainTerm parameter : parameters) {
            newParameters.add(parameter
                    .uninterpretedFunctionsBackToArrayReads(arrayVars));
        }
        try {
            return UninterpretedPredicateInstance.create(function,
                    newParameters);
        } catch (WrongNumberOfParametersException exc) {
            throw new RuntimeException(
                    "Unexpected WrongNumberOfParametersException while back-substituting array reads.",
                    exc);
        } catch (WrongFunctionTypeException exc) {
            throw new RuntimeException(
                    "Unexpected WrongFunctionTypeException while back-substituting array reads.",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public UninterpretedPredicateInstance removeArrayITE(
            Formula topLevelFormula, Set<Token> noDependenceVars,
            Collection<Formula> constraints) {
        List<DomainTerm> newParams = new ArrayList<DomainTerm>(
                parameters.size());
        for (DomainTerm parameter : parameters) {
            newParams.add(parameter.removeArrayITE(topLevelFormula,
                    noDependenceVars, constraints));
        }
        try {
            return UninterpretedPredicateInstance.create(function, newParams);
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected exception while removing ArrayITEs.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeOut(java.io.BufferedWriter,
     *      at.iaik.suraq.util.HashTagContainer, boolean)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer,
            boolean handleThisWithTagContainer) throws IOException {
        if (handleThisWithTagContainer) {
            tagContainer.handle(this, writer);
        } else {
            writer.append('(').append(function.toString());
            writer.append(' ');
            for (DomainTerm parameter : parameters) {
                parameter.writeOut(writer, tagContainer);
                writer.append(' ');
            }
            writer.append(')');
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#writeOut(java.io.BufferedWriter,
     *      at.iaik.suraq.util.HashTagContainer)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer)
            throws IOException {
        writeOut(writer, tagContainer, true);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.append("(").append(function.toString());
        for (DomainTerm parameter : parameters) {
            writer.write(" ");
            parameter.writeTo(writer);
        }
        writer.append(")");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#writeTo(java.io.Writer,
     *      java.util.Map)
     */
    @Override
    public void writeTo(Writer writer, Map<SMTLibObject, String> definitions)
            throws IOException {
        writer.append("(").append(function.toString());
        for (DomainTerm parameter : parameters) {
            writer.write(" ");
            String id = definitions.get(parameter);
            assert (id != null);
            writer.write(id);
        }
        writer.append(")");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getLiterals(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getLiterals(Set<Formula> result, Set<Formula> done) {
        result.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#numAigNodes(java.util.Set)
     */
    @Override
    public int numAigNodes(Set<Formula> done) {
        return 0;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toAig(TreeMap, java.util.Map)
     */
    @Override
    public int toAig(TreeMap<Integer, Integer[]> aigNodes,
            Map<Formula, Integer> done) {
        assert (done.get(this) != null);
        return done.get(this);
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

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getTerms(java.util.Set,
     *      java.util.Set)
     */
    @Override
    public void getTerms(Set<Term> result, Set<Formula> done) {
        if (done.contains(this))
            return;

        result.addAll(parameters);

        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#dependsOnlyOn(java.util.Set)
     */
    @Override
    public boolean dependsOnlyOn(Set<Formula> formulaSet) {
        return true;
    }

}
