package at.iaik.suraq.main;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.PropositionalEq;
import at.iaik.suraq.smtlib.formula.PropositionalTerm;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.DebugHelper;

public class Ackermann {

    private static boolean _isActive = true;
    private static boolean _isPredicateActive = true;
    private static boolean _isFunctionActive = true;
    public static void setActive(boolean isActive)
    {
        _isActive = isActive;
    }
    public static boolean isActive()
    {
        return _isActive;
    }
    
    
	
	public Formula performAckermann(Formula topLevelFormula, Set<Token> noDependenceVars)
	{
	    // For Debugging issues you can deactivate the Ackermann's reduction by
	    // calling Ackermann.setActive(false);
	    if(!_isActive)
	    {
	        System.err.println("* WARNING: Didn't perform Ackermann, because it was deactivated.");
            System.err.println("* Use Ackermamnn.setActive(true) to activate the Ackermann's reduction.");
	        return topLevelFormula;
	    }

		// Get all UF-Names and store them to a set of Tokens.
        System.out.println("   Ackermann: getUninterpretedFunctionNames()");
		Set<Token> currentUninterpretedFunctions = new HashSet<Token>();
		
		UninterpretedPredicateInstance.method=_isPredicateActive;
        UninterpretedFunctionInstance.method=_isFunctionActive;
        for (String var : topLevelFormula.getUninterpretedFunctionNames())
            currentUninterpretedFunctions.add(Token.generate(var));
        UninterpretedPredicateInstance.method=true;
        UninterpretedFunctionInstance.method=true;
        // this adds UFs as well as UPs... as expected

        ////////////////////////////////////////////////////////////
		// Substitute UF by Variables
		if(_isFunctionActive){
            System.out.println("   Ackermann: uninterpretedFunctionsToAuxiliaryVariables(...)");
    		Map<String, List<DomainVariable>> functionInstances = new HashMap<String, List<DomainVariable>>();
    		Map<DomainVariable, List<DomainTerm>> instanceParameters = new HashMap<DomainVariable, List<DomainTerm>>();
            DebugHelper.getInstance().formulaToFile(topLevelFormula, "./debug_aux_func_before.txt");
    		topLevelFormula.uninterpretedFunctionsToAuxiliaryVariables(topLevelFormula, functionInstances, instanceParameters, noDependenceVars);
            DebugHelper.getInstance().formulaToFile(topLevelFormula, "./debug_aux_func_after.txt");
            
            // Add Constraints for these UFs
            System.out.println("   Ackermann: add UF-constraints(...)");
            List<Formula> constraintsList = new ArrayList<Formula>();
            addAckermannFunctionConstraints(topLevelFormula, constraintsList, functionInstances, instanceParameters);
            
            // Generate the Implies formula FC => !flat
            System.out.println("   Ackermann: ImpliesFormula(...)");
            if (constraintsList.size() > 0)
            {
                Formula ackermannConstraints = (constraintsList.size() == 1) 
                        ? constraintsList.iterator().next() 
                        : AndFormula.generate(constraintsList);
                        topLevelFormula = new ImpliesFormula(ackermannConstraints, topLevelFormula);
            }
            else
            {
                System.out.println("   Ackermann: There are no FunctionConstraints.");
            }
            
		}
		else
		{
		    System.err.println(" *** Warning: Ackermann didn't perform on Functions (disabled)");
		}
        

        ////////////////////////////////////////////////////////////

        if(_isPredicateActive){
    		// Init for UP
            // constraintsList = new ArrayList<Formula>();
    
    		// substitute UP by Variables
            System.out.println("   Ackermann: uninterpretedPredicatesToAuxiliaryVariables(...)");
    		Map<String, List<PropositionalVariable>> predicateInstances = new HashMap<String, List<PropositionalVariable>>();
    		Map<PropositionalVariable, List<DomainTerm>> instanceParametersPredicates = new HashMap<PropositionalVariable, List<DomainTerm>>();
    		
    
            DebugHelper.getInstance().formulaToFile(topLevelFormula, "./debug_aux_pred_before.txt");
    		topLevelFormula.uninterpretedPredicatesToAuxiliaryVariables(topLevelFormula, predicateInstances, instanceParametersPredicates, noDependenceVars);
            DebugHelper.getInstance().formulaToFile(topLevelFormula, "./debug_aux_pred_after.txt");
            
            
            System.out.println("   Ackermann: predicateInstances.size: "+predicateInstances.size());
            System.out.println("   Ackermann: instanceParametersPredicates.size: "+instanceParametersPredicates.size());
    		// Add Constraints for these UPs
            System.out.println("   Ackermann: addAckermannPredicateConstraints(...)");
            
            //HashSet<Formula> constraints = new HashSet<Formula>();
            List<Formula> constraintsList = new ArrayList<Formula>();
    		addAckermannPredicateConstraints(topLevelFormula, constraintsList, predicateInstances, instanceParametersPredicates);
    
            // Generate the Implies formula FC => !flat
    		if (constraintsList.size() > 0)
    		{
    		    Formula ackermannConstraints = (constraintsList.size() == 1)
    		            ? constraintsList.iterator().next()
    		            : AndFormula.generate(constraintsList);
                topLevelFormula = new ImpliesFormula(ackermannConstraints, topLevelFormula);
    		}
    		else
    		{
    		    System.out.println("   Ackermann: There are no PredicateConstraints.");
    		}
        }
        else
        {
            System.err.println(" *** Warning: Ackermann didn't perform on Predicates (disabled)");
        }
        
        // debug check:
        if(_isPredicateActive && _isFunctionActive)
        {
            assert(topLevelFormula.getUninterpretedFunctions().size()==0);
            if(topLevelFormula.getUninterpretedFunctions().size()!=0)
                System.err.println("asdfasdfasdfasdfasdfasdfasdfasdf");
        }

        ////////////////////////////////////////////////////////////
		
		// remove all UF and UP (?)
        System.out.println("   Ackermann: noDependenceVars.removeall(UF)");
        // DEBUG:
        /*
        System.err.flush();
        System.out.flush();
        System.out.println("   The following UF are noDependenceVars and can be deleted of that list:");
        System.err.println("   The following UF are not noDependenceVars and are not on that list:");
        for(Token t : currentUninterpretedFunctions)
        {
            if(noDependenceVars.contains(t))
            {
                System.out.println("      "+t);
            }
            else
            {
                System.err.println("      "+t);
            }
        }
        System.err.flush();
        System.out.flush();
        */
        System.out.println("    Anzahl der Variablen bevor dem Entfernen: "+noDependenceVars.size());
        System.out.println("    Entfernt werden sollten "+ currentUninterpretedFunctions.size() + "Variablen");
		noDependenceVars.removeAll(currentUninterpretedFunctions);
        // may remove too much (functions and predicates) if one is deactivated
        System.out.println("    Anzahl der Variablen nach dem Entfernen: "+noDependenceVars.size());

		// finished. return.
        System.out.println("   Ackermann: done - return.");
		return topLevelFormula;
	}
	
    
	/**
	 * Adds Ackermann constraints according to predicate-instance and
	 * instance-parameter mappings to the constraints.
	 * 
	 * @param formula
	 *            the main formula to expand
	 * @param constraints
	 *            the formula's constraints.
	 * @param predicatPropositionalVariableeInstances
	 *            map containing mapping from predicate names to auxiliary
	 *            variables.
	 * @param instanceParameters
	 *            map containing mapping from auxiliary variables to predicate
	 *            instance parameters.
	 */
	private void addAckermannPredicateConstraints(Formula formula,
			//Set<Formula> constraints,
            List<Formula> constraints,
			Map<String, List<PropositionalVariable>> predicateInstances,
			Map<PropositionalVariable, List<DomainTerm>> instanceParameters) {

		for (Map.Entry<String, List<PropositionalVariable>> entry : predicateInstances.entrySet()) {

			List<PropositionalVariable> instances = entry.getValue();

			for (int i = 0; i < instances.size(); i++)
				for (int j = (i + 1); j < instances.size(); j++) {

					List<DomainTerm> params1 = instanceParameters.get(instances.get(i));
					List<DomainTerm> params2 = instanceParameters.get(instances.get(j));

					List<Formula> parametersEq = new ArrayList<Formula>();
					for (int k = 0; k < params1.size(); k++) {

						// Compute functional consistency constraints
						List<DomainTerm> list = new ArrayList<DomainTerm>();
						list.add(params1.get(k));
						list.add(params2.get(k));
						parametersEq.add(new DomainEq(list, true));

					}
					Formula parametersEquivalities;
					if (parametersEq.size() > 1)
						parametersEquivalities = AndFormula.generate(parametersEq);
					else
						parametersEquivalities = parametersEq.iterator().next();

					List<PropositionalTerm> predicateEq = new ArrayList<PropositionalTerm>();
					predicateEq.add(instances.get(i));
					predicateEq.add(instances.get(j));
					constraints.add(new ImpliesFormula(parametersEquivalities, new PropositionalEq(predicateEq, true)));

				}
		}
	}
    
    
	/**
	 * Adds Ackermann constraints according to function-instance and
	 * instance-parameter mappings to the constraints.
	 * 
	 * @param formula
	 *            the main formula to expand
	 * @param constraints
	 *            the formula's constraints.
	 * @param functionInstances
	 *            map containing mapping from function names to auxiliary
	 *            variables.
	 * @param instanceParameters
	 *            map containing mapping from auxiliary variables to function
	 *            instance parameters.
	 */
	private void addAckermannFunctionConstraints(Formula formula,
			List<Formula> constraints,
			Map<String, List<DomainVariable>> functionInstances,
			Map<DomainVariable, List<DomainTerm>> instanceParameters) {

		for (Map.Entry<String, List<DomainVariable>> entry : functionInstances.entrySet())
		{
			List<DomainVariable> instances = entry.getValue();

			for (int i = 0; i < instances.size(); i++)
				for (int j = (i + 1); j < instances.size(); j++) {
					// System.out.println(""+instances.get(i).getVarName()+" with "+instances.get(j).getVarName());

					List<DomainTerm> params1 = instanceParameters.get(instances.get(i));
					List<DomainTerm> params2 = instanceParameters.get(instances.get(j));

					List<Formula> parametersEq = new ArrayList<Formula>();
					for (int k = 0; k < params1.size(); k++)
					{
						// System.out.println("   "+t1.get(k)+"^"+t2.get(k));

						// Compute functional consistency constraints
						List<DomainTerm> list = new ArrayList<DomainTerm>();
						list.add(params1.get(k));
						list.add(params2.get(k));
						parametersEq.add(new DomainEq(list, true));
					}
					Formula parametersEquivalities = (parametersEq.size() > 1)
					        ? AndFormula.generate(parametersEq)
					        : parametersEq.iterator().next();
					
					List<DomainTerm> functionEq = new ArrayList<DomainTerm>();
					functionEq.add(instances.get(i));
					functionEq.add(instances.get(j));
					constraints.add(
					        new ImpliesFormula(parametersEquivalities, new DomainEq(functionEq, true)));

				}
		}
	}
    public static boolean isFunctionActive() {
        return _isFunctionActive;
    }
    public static void setFunctionActive(boolean _isFunctionActive) {
        Ackermann._isFunctionActive = _isFunctionActive;
    }
    public static boolean isPredicateActive() {
        return _isPredicateActive;
    }
    public static void setPredicateActive(boolean _isPredicateActive) {
        Ackermann._isPredicateActive = _isPredicateActive;
    }
}
