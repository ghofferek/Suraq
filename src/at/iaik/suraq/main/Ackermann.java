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

public class Ackermann {

    private static boolean _isActive = true;
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
	    
	    // Init
	    System.out.println("   Ackermann start");
		HashSet<Formula> constraints = new HashSet<Formula>();
		List<Formula> constraintsList = new ArrayList<Formula>();

		// Get all UF-Names and store them to a set of Tokens.
        System.out.println("   Ackermann: getUninterpretedFunctionNames()");
		Set<Token> currentUninterpretedFunctions = new HashSet<Token>();
		for (String var : topLevelFormula.getUninterpretedFunctionNames())
			currentUninterpretedFunctions.add(new Token(var));
		// this adds UFs as well as UPs... as expected


        ////////////////////////////////////////////////////////////
		// Substitute UF by Variables
        System.out.println("   Ackermann: uninterpretedFunctionsToAuxiliaryVariables(...)");
		Map<String, List<DomainVariable>> functionInstances = new HashMap<String, List<DomainVariable>>();
		Map<DomainVariable, List<DomainTerm>> instanceParameters = new HashMap<DomainVariable, List<DomainTerm>>();
		topLevelFormula.uninterpretedFunctionsToAuxiliaryVariables(topLevelFormula, functionInstances, instanceParameters, noDependenceVars);

		// Add Constraints for these UFs
        System.out.println("   Ackermann: add UF-constraints(...)");
		addAckermannFunctionConstraints(topLevelFormula, constraintsList, functionInstances, instanceParameters);
		
		// Generate the Implies formula FC => !flat
        System.out.println("   Ackermann: ImpliesFormula(...)");
        Formula ackermannConstraints;
		if (constraintsList.size() > 0)
		{
			ackermannConstraints = (constraintsList.size() == 1) 
			        ? constraintsList.iterator().next() 
			        : new AndFormula(constraintsList);
			        topLevelFormula = new ImpliesFormula(ackermannConstraints, topLevelFormula);
		}
		
		
		////////////////////////////////////////////////////////////
		// Init for UP
        // constraintsList = new ArrayList<Formula>();
        constraintsList.clear();

		// substitute UP by Variables
        System.out.println("   Ackermann: uninterpretedPredicatesToAuxiliaryVariables(...)");
		Map<String, List<PropositionalVariable>> predicateInstances = new HashMap<String, List<PropositionalVariable>>();
		Map<PropositionalVariable, List<DomainTerm>> instanceParametersPredicates = new HashMap<PropositionalVariable, List<DomainTerm>>();
		topLevelFormula.uninterpretedPredicatesToAuxiliaryVariables(topLevelFormula, predicateInstances, instanceParametersPredicates, noDependenceVars);

		// Add Constraints for these UPs
        System.out.println("   Ackermann: addAckermannPredicateConstraints(...)");
		addAckermannPredicateConstraints(topLevelFormula, constraints, predicateInstances, instanceParametersPredicates);

        // Generate the Implies formula FC => !flat
		if (constraintsList.size() > 0)
		{
		    ackermannConstraints = (constraintsList.size() == 1)
		            ? constraintsList.iterator().next()
		            : new AndFormula(constraintsList);
            topLevelFormula = new ImpliesFormula(ackermannConstraints, topLevelFormula);
		}
        ////////////////////////////////////////////////////////////
		
		// remove all UF and UP (?)
        System.out.println("   Ackermann: noDependenceVars.removeall(UF)");

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
        
        System.out.println("    Anzahl der Variablen bevor dem Entfernen: "+noDependenceVars.size());
        System.out.println("    Entfernt werden sollten "+ currentUninterpretedFunctions.size() + "Variablen");
		noDependenceVars.removeAll(currentUninterpretedFunctions);
        System.out.println("    Anzahl der Variablen nach dem Entfernen: "+noDependenceVars.size());
        System.out.println("    Sollte diese Rechnung nicht aufgehen, stimmt das mit dem new Term(name) oben nicht.");

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
			Set<Formula> constraints,
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
						parametersEquivalities = new AndFormula(parametersEq);
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
					        ? new AndFormula(parametersEq)
					        : parametersEq.iterator().next();
					
					List<DomainTerm> functionEq = new ArrayList<DomainTerm>();
					functionEq.add(instances.get(i));
					functionEq.add(instances.get(j));
					constraints.add(
					        new ImpliesFormula(parametersEquivalities, new DomainEq(functionEq, true)));

				}
		}
	}
}
