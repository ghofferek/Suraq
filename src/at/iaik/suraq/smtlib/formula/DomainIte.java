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

import javax.xml.ws.Holder;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.HashTagContainer;
import at.iaik.suraq.util.Util;

/**
 * An if-then-else-style domain term.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class DomainIte extends DomainTerm {

    /**
     * 
     */
    private static final long serialVersionUID = -5183742886536916272L;

    /**
     * The condition.
     */
    private final Formula condition;

    /**
     * The then-branch.
     */
    private final DomainTerm thenBranch;

    /**
     * The else-branch
     */
    private final DomainTerm elseBranch;

    /**
     * 
     * Constructs a new <code>DomainIte</code>.
     * 
     * @param condition
     *            the condition
     * @param thenBranch
     *            the value of the then-branch
     * @param elseBranch
     *            the value of the else-branch
     */
    private DomainIte(Formula condition, DomainTerm thenBranch,
            DomainTerm elseBranch) {
        if (condition instanceof FormulaTerm)
            this.condition = ((FormulaTerm) condition).getFormula();
        else
            this.condition = condition;
        this.thenBranch = thenBranch;
        this.elseBranch = elseBranch;
    }

    public static DomainIte create(Formula condition, DomainTerm thenBranch,
            DomainTerm elseBranch) {
        return (DomainIte) FormulaCache.domainTerm.put(new DomainIte(condition,
                thenBranch, elseBranch));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        // not applicable to DomainIte
        return false;
    }

    /**
     * Returns the condition.
     * 
     * @return the <code>condition</code>
     */
    public Formula getCondition() {
        return condition;
    }

    /**
     * Returns the then branch.
     * 
     * @return the <code>thenBranch</code>
     */
    public DomainTerm getThenBranch() {
        return thenBranch;
    }

    /**
     * Returns the else branch.
     * 
     * @return the <code>elseBranch</code>
     */
    public DomainTerm getElseBranch() {
        return elseBranch;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public DomainTerm deepTermCopy() {
        return this; // experimental
        // return new DomainIte(condition.deepFormulaCopy(),
        // thenBranch.deepTermCopy(), elseBranch.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getArrayVariables(result, done);
        elseBranch.getArrayVariables(result, done);
        condition.getArrayVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public void getDomainVariables(Set<DomainVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getDomainVariables(result, done);
        elseBranch.getDomainVariables(result, done);
        condition.getDomainVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public void getPropositionalVariables(Set<PropositionalVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getPropositionalVariables(result, done);
        elseBranch.getPropositionalVariables(result, done);
        condition.getPropositionalVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getFunctionMacroNames(result, done);
        elseBranch.getFunctionMacroNames(result, done);
        condition.getFunctionMacroNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public void getFunctionMacros(Set<FunctionMacro> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getFunctionMacros(result, done);
        elseBranch.getFunctionMacros(result, done);
        condition.getFunctionMacros(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getUninterpretedFunctionNames(result, done);
        elseBranch.getUninterpretedFunctionNames(result, done);
        condition.getUninterpretedFunctionNames(result, done);
        done.add(this);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof DomainIte))
            return false;

        if (this.hashCode() != obj.hashCode())
            return false;

        return ((DomainIte) obj).thenBranch.equals(thenBranch)
                && ((DomainIte) obj).elseBranch.equals(elseBranch)
                && ((DomainIte) obj).condition.equals(condition);

    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return condition.hashCode() * 31 * 31 + thenBranch.hashCode() * 31
                + elseBranch.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        result.addAll(thenBranch.getIndexSet());
        result.addAll(elseBranch.getIndexSet());
        result.addAll(condition.getIndexSet());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.containsKey(this)) {
            assert (done.get(this) != null);
            assert (done.get(this) instanceof Term);
            return (Term) done.get(this);
        }
        DomainTerm convertedThenBranch = (DomainTerm) thenBranch
                .substituteTerm(paramMap, done);
        DomainTerm convertedElseBranch = (DomainTerm) elseBranch
                .substituteTerm(paramMap, done);
        Formula convertedCondition = condition
                .substituteFormula(paramMap, done);

        Term result = DomainIte.create(convertedCondition, convertedThenBranch,
                convertedElseBranch);
        assert (result != null);
        done.put(this, result);
        return result;
    }

    /**
     * Simplifies this term by first simplifying the condition, and subsequently
     * simplifying the ite, if the condition is a constant.
     * 
     * @return a <code>DomainIte</code> term, which is simplified. Unchanged
     *         parts are not copied.
     */
    public DomainTerm simplify() {

        Formula simplifiedCondition = condition.simplify();

        if (simplifiedCondition instanceof PropositionalConstant)
            if (((PropositionalConstant) simplifiedCondition).getValue())
                return thenBranch;
            else
                return elseBranch;

        if (thenBranch.equals(elseBranch))
            return thenBranch;

        return DomainIte.create(simplifiedCondition, thenBranch, elseBranch);
    }

    /**
     * @return a flattened copy of this term.
     */
    @Override
    public DomainTerm flatten() {
        return DomainIte.create(condition.flatten(),
                (DomainTerm) thenBranch.flatten(),
                (DomainTerm) elseBranch.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        SExpression[] expr = new SExpression[4];
        expr[0] = SExpressionConstants.ITE;
        expr[1] = condition.toSmtlibV2();
        expr[2] = thenBranch.toSmtlibV2();
        expr[3] = elseBranch.toSmtlibV2();
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Term arrayPropertiesToFiniteConjunctionsTerm(Set<DomainTerm> indexSet) {
        Formula condition = this.condition
                .arrayPropertiesToFiniteConjunctions(indexSet);
        DomainTerm thenBranch = (DomainTerm) this.thenBranch
                .arrayPropertiesToFiniteConjunctionsTerm(indexSet);
        DomainTerm elseBranch = (DomainTerm) this.elseBranch
                .arrayPropertiesToFiniteConjunctionsTerm(indexSet);
        return DomainIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayEqualitiesTerm()
     */
    @Override
    public Term removeArrayEqualitiesTerm() {
        Formula condition = this.condition.removeArrayEqualities();
        DomainTerm thenBranch = (DomainTerm) this.thenBranch
                .removeArrayEqualitiesTerm();
        DomainTerm elseBranch = (DomainTerm) this.elseBranch
                .removeArrayEqualitiesTerm();
        return DomainIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Formula condition = this.condition.removeArrayWrites(topLevelFormula,
                constraints, noDependenceVars);
        DomainTerm thenBranch = (DomainTerm) this.thenBranch
                .removeArrayWritesTerm(topLevelFormula, constraints,
                        noDependenceVars);
        DomainTerm elseBranch = (DomainTerm) this.elseBranch
                .removeArrayWritesTerm(topLevelFormula, constraints,
                        noDependenceVars);
        return DomainIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(
            Set<Token> noDependenceVars) {
        Formula condition = this.condition
                .arrayReadsToUninterpretedFunctions(noDependenceVars);
        DomainTerm thenBranch = this.thenBranch;
        DomainTerm elseBranch = this.elseBranch;

        if (thenBranch instanceof ArrayRead)
            thenBranch = ((ArrayRead) thenBranch)
                    .toUninterpretedFunctionInstance(noDependenceVars);
        else
            thenBranch = (DomainTerm) thenBranch
                    .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);

        if (elseBranch instanceof ArrayRead)
            elseBranch = ((ArrayRead) elseBranch)
                    .toUninterpretedFunctionInstance(noDependenceVars);
        else
            elseBranch = (DomainTerm) elseBranch
                    .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);
        return DomainIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        thenBranch.getUninterpretedFunctions(result, done);
        elseBranch.getUninterpretedFunctions(result, done);
        condition.getUninterpretedFunctions(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public DomainTerm substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null) {
            assert (done.get(this) instanceof Term);
            return (DomainTerm) done.get(this);
        }
        Formula condition = this.condition.substituteUninterpretedFunction(
                substitutions, done);
        DomainTerm thenBranch = this.thenBranch
                .substituteUninterpretedFunction(substitutions, done);
        DomainTerm elseBranch = this.elseBranch
                .substituteUninterpretedFunction(substitutions, done);
        DomainTerm result = DomainIte.create(condition, thenBranch, elseBranch);
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Formula condition = this.condition.makeArrayReadsSimple(
                topLevelFormula, constraints, noDependenceVars);
        DomainTerm thenBranch = (DomainTerm) this.thenBranch
                .makeArrayReadsSimpleTerm(topLevelFormula, constraints,
                        noDependenceVars);
        DomainTerm elseBranch = (DomainTerm) this.elseBranch
                .makeArrayReadsSimpleTerm(topLevelFormula, constraints,
                        noDependenceVars);
        return DomainIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public DomainTerm uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { return new DomainIte(
     * condition.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars),
     * thenBranch.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars),
     * elseBranch.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars)); }
     */

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = condition.getPartitionsFromSymbols();
        partitions.addAll(thenBranch.getPartitionsFromSymbols());
        partitions.addAll(elseBranch.getPartitionsFromSymbols());

        return partitions;
    }

    /**
     * @see at.iaik.suraq.formula.DomainTerm#uninterpretedPredicatesToAuxiliaryVariables(t)
     */
    @Override
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        Formula condition = this.condition;
        DomainTerm thenBranch = this.thenBranch;
        DomainTerm elseBranch = this.elseBranch;

        if (condition instanceof UninterpretedPredicateInstance)
            condition = ((UninterpretedPredicateInstance) condition)
                    .applyReplaceUninterpretedPredicates(topLeveFormula,
                            predicateInstances, instanceParameters,
                            noDependenceVars);
        else
            condition = condition.uninterpretedPredicatesToAuxiliaryVariables(
                    topLeveFormula, predicateInstances, instanceParameters,
                    noDependenceVars);

        thenBranch = (DomainTerm) thenBranch
                .uninterpretedPredicatesToAuxiliaryVariablesTerm(
                        topLeveFormula, predicateInstances, instanceParameters,
                        noDependenceVars);

        elseBranch = (DomainTerm) elseBranch
                .uninterpretedPredicatesToAuxiliaryVariablesTerm(
                        topLeveFormula, predicateInstances, instanceParameters,
                        noDependenceVars);
        return DomainIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.formula.DomainTerm#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {
        Formula condition = this.condition;
        DomainTerm thenBranch = this.thenBranch;
        DomainTerm elseBranch = this.elseBranch;

        condition = condition.uninterpretedFunctionsToAuxiliaryVariables(
                topLeveFormula, functionInstances, instanceParameters,
                noDependenceVars);

        if (thenBranch instanceof UninterpretedFunctionInstance)
            thenBranch = ((UninterpretedFunctionInstance) thenBranch)
                    .applyReplaceUninterpretedFunctions(topLeveFormula,
                            functionInstances, instanceParameters,
                            noDependenceVars);
        else
            thenBranch = (DomainTerm) thenBranch
                    .uninterpretedFunctionsToAuxiliaryVariablesTerm(
                            topLeveFormula, functionInstances,
                            instanceParameters, noDependenceVars);

        if (elseBranch instanceof UninterpretedFunctionInstance)
            elseBranch = ((UninterpretedFunctionInstance) elseBranch)
                    .applyReplaceUninterpretedFunctions(topLeveFormula,
                            functionInstances, instanceParameters,
                            noDependenceVars);
        else
            elseBranch = (DomainTerm) elseBranch
                    .uninterpretedFunctionsToAuxiliaryVariablesTerm(
                            topLeveFormula, functionInstances,
                            instanceParameters, noDependenceVars);
        return DomainIte.create(condition, thenBranch, elseBranch);

    }

    @Deprecated
    public Formula removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Holder<Term> newToken,
            List<Formula> andPreList) {
        List<Formula> _andlist = new ArrayList<Formula>();
        // generate a new Var that shall replace the original one

        // remember that "ite" is a reserved word!
        // Hence I used "itev" instead for ite variable
        Token newDomainToken = Token.generate(Util.freshVarNameCached(
                topLevelFormula, "itev"));
        DomainVariable newDomainVar = DomainVariable.create(newDomainToken);
        newToken.value = newDomainVar;

        // remove DomainITE recusively -> also condition, then, else
        Formula condition = this.condition.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        DomainTerm elseBranch = this.elseBranch;
        DomainTerm thenBranch = this.thenBranch;
        if (elseBranch instanceof DomainIte) {
            Holder<Term> newToken2 = new Holder<Term>();
            _andlist.add(((DomainIte) elseBranch).removeDomainITE(
                    topLevelFormula, noDependenceVars, newToken2, andPreList));
            elseBranch = (DomainVariable) newToken2.value;
        }
        if (thenBranch instanceof DomainIte) {
            Holder<Term> newToken2 = new Holder<Term>();
            _andlist.add(((DomainIte) thenBranch).removeDomainITE(
                    topLevelFormula, noDependenceVars, newToken2, andPreList));
            thenBranch = (DomainVariable) newToken2.value;
        }

        HashSet<DomainVariable> innerVariables = new HashSet<DomainVariable>();
        HashSet<SMTLibObject> done = new HashSet<SMTLibObject>();
        elseBranch.getDomainVariables(innerVariables, done);
        thenBranch.getDomainVariables(innerVariables, done);
        condition.getDomainVariables(innerVariables, done);
        for (DomainVariable dv : innerVariables) {
            if (noDependenceVars.contains(dv)) {
                // System.err.println("new nodependencyvar: " + newDomainToken);
                noDependenceVars.add(newDomainToken);
                break;
            }
        }
        // System.err.println(".");

        // generate a new Formula out of: ITE(condition, then, else)
        // make: itevar
        // later do: ITE(condition, itevar=then, itevar=else)
        try {
            List<Term> _thenlist = new ArrayList<Term>();
            _thenlist.add(thenBranch);
            _thenlist.add(newDomainVar);
            Formula _then = EqualityFormula.create(_thenlist, true);

            List<Term> _elselist = new ArrayList<Term>();
            _elselist.add(elseBranch);
            _elselist.add(newDomainVar);
            Formula _else = EqualityFormula.create(_elselist, true);

            Formula newPropFormula = PropositionalIte.create(condition, _then,
                    _else);

            // if the toplevelFormula is an AndFormula, we can reuse it.
            /*
             * if(topLevelFormula instanceof AndFormula) {
             * ((AndFormula)topLevelFormula).addFormula(newPropFormula); } else
             * { // append the ITE to the end of the formula List<Formula>
             * _andlist = new ArrayList<Formula>();
             * _andlist.add(topLevelFormula); _andlist.add(newPropFormula);
             * topLevelFormula = new AndFormula(_andlist); }
             */

            if (_andlist.size() == 0) {
                return newPropFormula;
            } else {
                // return new ImpliesFormula(new
                // AndFormula(_andlist),newPropFormula);
                _andlist.add(newPropFormula);

                return AndFormula.generate(_andlist);
            }
        } catch (Exception ex) {
            ex.printStackTrace();
            throw new RuntimeException("Unexpected Exception.");
        }

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public DomainTerm uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars, Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null)
            return (DomainTerm) done.get(this);
        DomainTerm result = DomainIte.create((Formula) condition
                .uninterpretedFunctionsBackToArrayReads(arrayVars, done),
                (DomainTerm) thenBranch.uninterpretedFunctionsBackToArrayReads(
                        arrayVars, done),
                (DomainTerm) elseBranch.uninterpretedFunctionsBackToArrayReads(
                        arrayVars, done));
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#removeDomainITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.List)
     */
    @Override
    public DomainTerm removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        Token newToken = Token.generate(Util.freshVarNameCached(
                topLevelFormula, "itev"));
        DomainVariable newVar = DomainVariable.create(newToken);

        List<DomainTerm> termsThen = new ArrayList<DomainTerm>(2);
        List<DomainTerm> termsElse = new ArrayList<DomainTerm>(2);
        termsThen.add(newVar);
        termsThen.add(thenBranch.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList));
        termsElse.add(newVar);
        termsElse.add(elseBranch.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList));
        try {
            DomainEq eqThen = (DomainEq) EqualityFormula
                    .create(termsThen, true);
            DomainEq eqElse = (DomainEq) EqualityFormula
                    .create(termsElse, true);
            PropositionalIte propIte = PropositionalIte.create(condition
                    .removeDomainITE(topLevelFormula, noDependenceVars,
                            andPreList), eqThen, eqElse);
            // if (Util.formulaContainsAny(propIte, noDependenceVars))
            // Always make new auxiliary variables noDep, to avoid combinational
            // loops
            noDependenceVars.add(newToken);
            andPreList.add(propIte);
            return newVar;
        } catch (SuraqException exc) {
            throw new RuntimeException(
                    "Unexpected exception while removing DomainITEs.", exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public DomainIte removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        Formula newCondition = condition.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        DomainTerm newThenBranch = thenBranch.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        DomainTerm newElseBranch = elseBranch.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        return DomainIte.create(newCondition, newThenBranch, newElseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#writeOut(java.io.BufferedWriter,
     *      at.iaik.suraq.util.HashTagContainer, boolean)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer)
            throws IOException {

        writer.append('(').append(SExpressionConstants.ITE.toString());
        writer.append(' ');
        condition.writeOut(writer, tagContainer, true);
        writer.append(' ');
        thenBranch.writeOut(writer, tagContainer);
        writer.append(' ');
        elseBranch.writeOut(writer, tagContainer);
        writer.append(')');
    }

    /**
     * @throws IOException
     * @see at.iaik.suraq.smtlib.formula.Term#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.append('(').append(SExpressionConstants.ITE.toString());
        writer.append(' ');
        condition.writeTo(writer);
        writer.append(' ');
        thenBranch.writeTo(writer);
        writer.append(' ');
        elseBranch.writeTo(writer);
        writer.append(')');

    }

}
