/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;

/**
 * A common superclass for And- Or- and Xor-formulas to avoid code redundancy.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class AndOrXorFormula extends BooleanCombinationFormula {
    /**
     * 
     */
    private static final long serialVersionUID = 3515032983832421411L;
    /**
     * The list of sub-formulas.
     */
    protected final List<Formula> formulas;

    
    /**
     * 
     * Constructs a new <code>AndOrXorFormula</code>. Initializes the list of
     * subformulas.
     * 
     * @param formulas
     *            the list of subformulas.
     */
    protected AndOrXorFormula(List<? extends Formula> formulas) {
        this.formulas = new ArrayList<Formula>();
        for (Formula formula : formulas) {
            if (formula instanceof FormulaTerm)
                this.formulas.add(((FormulaTerm) formula).getFormula());
            else
                this.formulas.add(formula);
        }
        if (formulas.size() < 1)
            this.formulas.add(new PropositionalConstant(true));
    }

    /**
     * Creates a new <code>AndOrXorFormula</code> which is of the same type as
     * <code>this</code> object and has the given subformulas.
     * 
     * @param formulas
     *            the subformulas
     * @return a new <code>AndOrXorFormula</code> with the same type as
     *         <code>this</code>.
     */
    protected AndOrXorFormula create(List<? extends Formula> formulas) {
        Class<? extends AndOrXorFormula> myClass = this.getClass();
        // Class<?> listClass = formulas.getClass();
        AndOrXorFormula instance = null;
        try {
            Constructor<?>[] constructors = myClass.getDeclaredConstructors();
            if (constructors.length == 0)
                throw new RuntimeException("No constructors found.");
            for (Constructor<?> constructor : constructors) {
                Class<?>[] parameters = constructor.getParameterTypes();
                if (parameters.length != 1)
                    continue;
                if (!(parameters[0].isInstance(formulas)))
                    continue;
                instance = (AndOrXorFormula) constructor.newInstance(formulas);
            }
            if (instance == null)
                throw new RuntimeException();
            return instance;
        } catch (Throwable exc) {
        	exc.printStackTrace();
            throw new RuntimeException("Unable to create AndOrXorFormula", exc);
        }
        // TODO: cache!!!
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getArrayVariables()
     */
    @Override
    public Set<ArrayVariable> getArrayVariables() {
        Set<ArrayVariable> variables = new HashSet<ArrayVariable>();
        for (Formula formula : formulas)
            variables.addAll(formula.getArrayVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getDomainVariables()
     */
    @Override
    public Set<DomainVariable> getDomainVariables() {
        Set<DomainVariable> variables = new HashSet<DomainVariable>();
        for (Formula formula : formulas)
            variables.addAll(formula.getDomainVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getPropositionalVariables()
     */
    @Override
    public Set<PropositionalVariable> getPropositionalVariables() {
        Set<PropositionalVariable> variables = new HashSet<PropositionalVariable>();
        for (Formula formula : formulas)
            variables.addAll(formula.getPropositionalVariables());
        return variables;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.BooleanCombinationFormula#getSubFormulas()
     */
    @Override
    public Collection<Formula> getSubFormulas() {
        return new ArrayList<Formula>(formulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#deepFormulaCopy()
     */
    @Override
    public Formula deepFormulaCopy() {
        List<Formula> subformulas = new ArrayList<Formula>();
        for (Formula formula : formulas) {
            if (formula == null)
                System.out.println(formula);

            subformulas.add(formula.deepFormulaCopy());
        }
        return create(subformulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#negationNormalForm()
     */
    @Override
    public Formula negationNormalForm() throws SuraqException {
        List<Formula> nnfFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            nnfFormulas.add(formula.negationNormalForm());

        return create(nnfFormulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctionNames()
     */
    @Override
    public Set<String> getUninterpretedFunctionNames() {
        Set<String> functionNames = new HashSet<String>();
        for (Formula formula : formulas)
            functionNames.addAll(formula.getUninterpretedFunctionNames());
        return functionNames;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacroNames()
     */
    @Override
    public Set<String> getFunctionMacroNames() {
        Set<String> macroNames = new HashSet<String>();
        for (Formula formula : formulas)
            macroNames.addAll(formula.getFunctionMacroNames());
        return macroNames;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getFunctionMacros()
     */
    @Override
    public Set<FunctionMacro> getFunctionMacros() {
        Set<FunctionMacro> macros = new HashSet<FunctionMacro>();
        for (Formula formula : formulas)
            macros.addAll(formula.getFunctionMacros());
        return macros;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        Set<DomainTerm> indexSet = new HashSet<DomainTerm>();
        for (Formula formula : formulas)
            indexSet.addAll(formula.getIndexSet());
        return indexSet;
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;

        if (this.hashCode() != obj.hashCode())
            return false;

        if (!(this.getClass().isInstance(obj)))
            return false;

        return this.formulas.equals(((AndOrXorFormula) obj).formulas);

    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        /*
        int hashCode = 0;
        for (Formula formula : formulas)
            hashCode ^= formula.hashCode();
        */
        return formulas.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteFormula(Map)
     */
    @Override
    public Formula substituteFormula(Map<Token, ? extends Term> paramMap) {
        List<Formula> convertedFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            convertedFormulas.add(formula.substituteFormula(paramMap));

        return create(convertedFormulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayEqualitiesTerm()
     */
    @Override
    public Formula removeArrayEqualities() {
        AndOrXorFormula secondInstance = create(formulas);
        for (int count = 0; count < secondInstance.formulas.size(); count++) {
            if (secondInstance.formulas.get(count) instanceof ArrayEq)
                secondInstance.formulas.set(count,
                        ((ArrayEq) secondInstance.formulas.get(count))
                                .toArrayProperties());
            else
                secondInstance.formulas.set(count,
                        secondInstance.formulas.get(count)
                                .removeArrayEqualities());
        }
        return secondInstance;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Formula arrayPropertiesToFiniteConjunctions(Set<DomainTerm> indexSet) {
        AndOrXorFormula secondInstance = create(formulas);
        for (int count = 0; count < secondInstance.formulas.size(); count++) {
            if (secondInstance.formulas.get(count) instanceof ArrayProperty)
                secondInstance.formulas.set(count,
                        ((ArrayProperty) secondInstance.formulas.get(count))
                                .toFiniteConjunction(indexSet));
            else
                secondInstance.formulas.set(count,
                        secondInstance.formulas.get(count)
                                .arrayPropertiesToFiniteConjunctions(indexSet));
        }
        return secondInstance;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#simplify()
     */
    @Override
    public Formula simplify() {
        AndOrXorFormula secondInstance = create(formulas);
        // Default, unless a subclass has more clever method
        for (int count = 0; count < formulas.size(); count++)
            secondInstance.formulas.set(count, formulas.get(count).simplify());
        return secondInstance;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#flatten()
     */
    @Override
    public Formula flatten() {
        List<Formula> flattenedFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            flattenedFormulas.add(formula.flatten());

        return create(flattenedFormulas);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        List<SExpression> children = new ArrayList<SExpression>();
        children.add(this.getOperator());
        for (Formula formula : formulas)
            children.add(formula.toSmtlibV2());
        return new SExpression(children);
    }

    /**
     * Returns the token representing the operator (and/or/xor) of this formula.
     * 
     * @return The operator token.
     */
    protected abstract Token getOperator();

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Formula removeArrayWrites(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        List<Formula> children = new ArrayList<Formula>();
        for (Formula formula : this.getSubFormulas())
            children.add(formula.removeArrayWrites(topLevelFormula,
                    constraints, noDependenceVars));
        return create(children);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Formula arrayReadsToUninterpretedFunctions(Set<Token> noDependenceVars) {
        List<Formula> children = new ArrayList<Formula>();
        for (Formula formula : formulas)
            children.add(formula.arrayReadsToUninterpretedFunctions(noDependenceVars));
        return create(children);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#getUninterpretedFunctions()
     */
    @Override
    public Set<UninterpretedFunction> getUninterpretedFunctions() {
        Set<UninterpretedFunction> functionNames = new HashSet<UninterpretedFunction>();
        for (Formula formula : formulas)
            functionNames.addAll(formula.getUninterpretedFunctions());
        return functionNames;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Formula substituteUninterpretedFunction(Token oldFunction,
            UninterpretedFunction newFunction) {
        List<Formula> children = new ArrayList<Formula>();
        for (Formula formula : formulas)
            children.add(formula.substituteUninterpretedFunction(oldFunction, newFunction));
        return create(children);
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
        List<Formula> children = new ArrayList<Formula>();
        for (Formula formula : formulas)
            children.add(formula.makeArrayReadsSimple(topLevelFormula, constraints,
                    noDependenceVars));
        return create(children);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Formula#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
   /* @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Set<Formula> constraints,
            Set<Token> noDependenceVars) {
        List<Formula> newFormulas = new ArrayList<Formula>();
        for (Formula formula : formulas)
            newFormulas.add(formula
                    .uninterpretedPredicatesToAuxiliaryVariables(
                            topLeveFormula, constraints, noDependenceVars));

        return this.create(newFormulas);
    }*/

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = new TreeSet<Integer>();

        for (Formula formula : formulas)
            partitions.addAll(formula.getPartitionsFromSymbols());
        return partitions;
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
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Formula uninterpretedPredicatesToAuxiliaryVariables(
            Formula topLeveFormula, Map<String,List<PropositionalVariable>> predicateInstances, 
            Map<PropositionalVariable,List<DomainTerm>> instanceParameters, Set<Token> noDependenceVars) {
    	

    	AndOrXorFormula secondInstance = create(formulas);
    	Collection<Formula> subformulas = this.getSubFormulas();
		  
    	for (Formula formula : subformulas)
    		if (formula instanceof UninterpretedPredicateInstance){ 
				  
    			Formula auxVar = ((UninterpretedPredicateInstance) formula).applyReplaceUninterpretedPredicates(topLeveFormula,
    					predicateInstances, instanceParameters, noDependenceVars);
				  
    			// added by chille: 03.07.2012
    			secondInstance.formulas.set(secondInstance.formulas.indexOf(formula), auxVar);
				  
    			// removed by chille:
    			// formulas.remove(formula);
    			// formulas.add(auxVar);
    		}
    		else
    			secondInstance.formulas.set(secondInstance.formulas.indexOf(formula), formula.uninterpretedPredicatesToAuxiliaryVariables(
    					topLeveFormula, predicateInstances, instanceParameters, noDependenceVars)); 
    	return secondInstance;

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
        List<Formula> children = new ArrayList<Formula>();
        for (Formula formula : this.getSubFormulas())
            children.add(formula.uninterpretedFunctionsToAuxiliaryVariables(
                    topLeveFormula, functionInstances, instanceParameters,
                    noDependenceVars));
        return create(children);
    }
    

    @Override
    public Formula replaceEquivalences(Formula topLevelFormula, Map<EqualityFormula, String> replacements, Set<Token> noDependenceVars)
    {
        List<Formula> children = new ArrayList<Formula>();
        for(int i=0;i<formulas.size();i++)
            children.add(formulas.get(i).replaceEquivalences(topLevelFormula, replacements, noDependenceVars));
        return create(children);
    }

    @Override
    public Formula removeDomainITE(Formula topLevelFormula, Set<Token> noDependenceVars, List<Formula> andPreList)
    {
        List<Formula> children = new ArrayList<Formula>();
        for(int i=0;i<formulas.size();i++)
            
            children.add(formulas.get(i).removeDomainITE(topLevelFormula, noDependenceVars, andPreList));
        return create(children);
    }
}
