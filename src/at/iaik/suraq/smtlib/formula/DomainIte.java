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

import javax.xml.ws.Holder;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.util.FormulaCache;
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
        //        thenBranch.deepTermCopy(), elseBranch.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> result = thenBranch.getArrayVariables();
        result.addAll(elseBranch.getArrayVariables());
        result.addAll(condition.getArrayVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> result = thenBranch.getDomainVariables();
        result.addAll(elseBranch.getDomainVariables());
        result.addAll(condition.getDomainVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> result = thenBranch
                .getPropositionalVariables();
        result.addAll(elseBranch.getPropositionalVariables());
        result.addAll(condition.getPropositionalVariables());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> result = thenBranch.getFunctionMacroNames();
        result.addAll(elseBranch.getFunctionMacroNames());
        result.addAll(condition.getFunctionMacroNames());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> result = thenBranch.getFunctionMacros();
        result.addAll(elseBranch.getFunctionMacros());
        result.addAll(condition.getFunctionMacros());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> result = thenBranch.getUninterpretedFunctionNames();
        result.addAll(elseBranch.getUninterpretedFunctionNames());
        result.addAll(condition.getUninterpretedFunctionNames());
        return result;
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
    public Term substituteTerm(Map<Token, ? extends Term> paramMap) {
        DomainTerm convertedThenBranch = (DomainTerm) thenBranch
                .substituteTerm(paramMap);
        DomainTerm convertedElseBranch = (DomainTerm) elseBranch
                .substituteTerm(paramMap);
        Formula convertedCondition = condition.substituteFormula(paramMap);
        return DomainIte.create(convertedCondition, convertedThenBranch,
                convertedElseBranch);
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
        Formula condition = this.condition.removeArrayWrites(topLevelFormula, constraints,
                noDependenceVars);
        DomainTerm thenBranch = (DomainTerm) this.thenBranch.removeArrayWritesTerm(topLevelFormula, constraints,
                noDependenceVars);
        DomainTerm elseBranch = (DomainTerm) this.elseBranch.removeArrayWritesTerm(topLevelFormula, constraints,
                noDependenceVars);
        return DomainIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(Set<Token> noDependenceVars) {
        Formula condition = this.condition.arrayReadsToUninterpretedFunctions(noDependenceVars);
        DomainTerm thenBranch = this.thenBranch;
        DomainTerm elseBranch = this.elseBranch;
        
        if (thenBranch instanceof ArrayRead)
            thenBranch = ((ArrayRead) thenBranch)
                    .toUninterpretedFunctionInstance(noDependenceVars);
        else
            thenBranch = (DomainTerm)thenBranch.arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);

        if (elseBranch instanceof ArrayRead)
            elseBranch = ((ArrayRead) elseBranch)
                    .toUninterpretedFunctionInstance(noDependenceVars);
        else
            elseBranch = (DomainTerm)elseBranch.arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);
        return DomainIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> result = thenBranch
                .getUninterpretedFunctions();
        result.addAll(elseBranch.getUninterpretedFunctions());
        result.addAll(condition.getUninterpretedFunctions());
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Term substituteUninterpretedFunctionTerm(Map<Token, UninterpretedFunction> substitutions) {
        Formula condition = this.condition.substituteUninterpretedFunction(substitutions);
        DomainTerm thenBranch = (DomainTerm) this.thenBranch.substituteUninterpretedFunctionTerm(substitutions);
        DomainTerm elseBranch = (DomainTerm) this.elseBranch.substituteUninterpretedFunctionTerm(substitutions);
        return DomainIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        Formula condition = this.condition.makeArrayReadsSimple(topLevelFormula, constraints,
                noDependenceVars);
        DomainTerm thenBranch = (DomainTerm) this.thenBranch.makeArrayReadsSimpleTerm(topLevelFormula, constraints,
                noDependenceVars);
        DomainTerm elseBranch = (DomainTerm) this.elseBranch.makeArrayReadsSimpleTerm(topLevelFormula, constraints,
                noDependenceVars);
        return DomainIte.create(condition, thenBranch, elseBranch);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*@Override
    public DomainTerm uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        return new DomainIte(
                condition.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars),
                thenBranch.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars),
                elseBranch.uninterpretedPredicatesToAuxiliaryVariables(
                        topLeveFormula, constraints, noDependenceVars));
    }*/

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
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {  	

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
                .uninterpretedPredicatesToAuxiliaryVariablesTerm(topLeveFormula,
                        predicateInstances, instanceParameters,
                        noDependenceVars);

        elseBranch = (DomainTerm) elseBranch
                .uninterpretedPredicatesToAuxiliaryVariablesTerm(topLeveFormula,
                        predicateInstances, instanceParameters,
                        noDependenceVars);
        return DomainIte.create(condition, thenBranch, elseBranch);
    }
    
    
    
    /**
     * @see at.iaik.suraq.formula.DomainTerm#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula, Map<String,List<DomainVariable>> functionInstances, 
            Map<DomainVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
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
                    .uninterpretedFunctionsToAuxiliaryVariablesTerm(topLeveFormula,
                            functionInstances, instanceParameters,
                            noDependenceVars);

        if (elseBranch instanceof UninterpretedFunctionInstance)
            elseBranch = ((UninterpretedFunctionInstance) elseBranch)
                    .applyReplaceUninterpretedFunctions(topLeveFormula,
                            functionInstances, instanceParameters,
                            noDependenceVars);
        else
            elseBranch = (DomainTerm) elseBranch
                    .uninterpretedFunctionsToAuxiliaryVariablesTerm(topLeveFormula,
                            functionInstances, instanceParameters,
                            noDependenceVars);
        return DomainIte.create(condition, thenBranch, elseBranch);

    }
    

    // DO NOT USE WITH UF yet!!!
    public Formula removeDomainITE(Formula topLevelFormula, Set<Token> noDependenceVars, Holder<Term> newToken, List<Formula> andPreList)
    {
        List<Formula> _andlist = new ArrayList<Formula>();
        // generate a new Var that shall replace the original one
        
        // remember that "ite" is a reserved word!
        // Hence I used "itev" instead for ite variable
        Token newDomainToken = Token.generate(Util.freshVarNameCached(topLevelFormula, "itev"));
        DomainVariable newDomainVar = DomainVariable.create(newDomainToken);
        newToken.value = newDomainVar;
        
        // remove DomainITE recusively -> also condition, then, else
        Formula condition = this.condition.removeDomainITE(topLevelFormula, noDependenceVars, andPreList);
        DomainTerm elseBranch = this.elseBranch;
        DomainTerm thenBranch = this.thenBranch;
        if(elseBranch instanceof DomainIte)
        {
            Holder<Term> newToken2 = new Holder<Term>();
            _andlist.add(((DomainIte)elseBranch).removeDomainITE(topLevelFormula, noDependenceVars, newToken2, andPreList));
            elseBranch = (DomainVariable) newToken2.value;
        }
        if(thenBranch instanceof DomainIte)
        {
            Holder<Term> newToken2 = new Holder<Term>();
            _andlist.add(((DomainIte)thenBranch).removeDomainITE(topLevelFormula, noDependenceVars, newToken2, andPreList));
            thenBranch = (DomainVariable) newToken2.value;
        }


        HashSet<DomainVariable> innerVariables = new HashSet<DomainVariable>();
        innerVariables.addAll(elseBranch.getDomainVariables());
        innerVariables.addAll(thenBranch.getDomainVariables());
        innerVariables.addAll(condition.getDomainVariables());
        for(DomainVariable dv : innerVariables)
        {
            if(noDependenceVars.contains(dv))
            {
                System.err.println("new nodependencyvar: "+ newDomainToken);
                noDependenceVars.add(newDomainToken);
                break;
            }
        }
        System.err.println(".");

        // Check if this formula contains any noDependenceVars
        Set<DomainVariable> dv = this.getDomainVariables();
        for(Token noDepVar : noDependenceVars)
        {
            if(dv.contains(noDepVar))
            {
                noDependenceVars.add(newDomainToken);
                break;
            }
        }
        
        // generate a new Formula out of: ITE(condition, then, else)
        // make:      itevar
        // later do:  ITE(condition, itevar=then, itevar=else)
        try{
            List<Term> _thenlist = new ArrayList<Term>();
            _thenlist.add(thenBranch);
            _thenlist.add(newDomainVar);
            Formula _then = EqualityFormula.create(_thenlist, true);
            
    
            List<Term> _elselist = new ArrayList<Term>();
            _elselist.add(elseBranch);
            _elselist.add(newDomainVar);
            Formula _else = EqualityFormula.create(_elselist, true);
    
            Formula newPropFormula = PropositionalIte.create(condition, _then, _else);
            
            // if the toplevelFormula is an AndFormula, we can reuse it.
            /*if(topLevelFormula instanceof AndFormula)
            {
                ((AndFormula)topLevelFormula).addFormula(newPropFormula);
            }
            else
            {
                // append the ITE to the end of the formula
                List<Formula> _andlist = new ArrayList<Formula>();
                _andlist.add(topLevelFormula);
                _andlist.add(newPropFormula);
                topLevelFormula = new AndFormula(_andlist);
            }*/
            
            if(_andlist.size() == 0)
            {
                return newPropFormula;
            }
            else
            {
                //return new ImpliesFormula(new AndFormula(_andlist),newPropFormula);
                _andlist.add(newPropFormula);
                
                return AndFormula.generate(_andlist);
            }
        }
        catch(Exception ex)
        {
            ex.printStackTrace();
            throw new RuntimeException("Unexpected Exception.");
        }
        
    }
}
 