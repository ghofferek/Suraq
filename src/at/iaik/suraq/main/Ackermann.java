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

	
	public Formula performAckermann(Formula formula, Set<Token> noDependenceVars)
	{
	    System.out.println("   Ackermann start");
		HashSet<Formula> constraints = new HashSet<Formula>();
		List<Formula> constraintsList = new ArrayList<Formula>();

		//noDependenceVars.remove(lambdaToken);  //remove lambda from list???

        System.out.println("   Ackermann: getUninterpretedFunctionNames");
		Set<Token> currentUninterpretedFunctions = new HashSet<Token>();
		for (String var : formula.getUninterpretedFunctionNames())
			currentUninterpretedFunctions.add(new Token(var));

        System.out.println("   Ackermann: uninterpretedFunctionsToAuxiliaryVariables");
		//System.out.println("Applying Ackermann reduction to remove uninterpreted-functions...");
		Map<String, List<DomainVariable>> functionInstances = new HashMap<String, List<DomainVariable>>();
		Map<DomainVariable, List<DomainTerm>> instanceParameters = new HashMap<DomainVariable, List<DomainTerm>>();
		formula.uninterpretedFunctionsToAuxiliaryVariables(formula,
				functionInstances, instanceParameters, noDependenceVars);

        System.out.println("   Ackermann: add UF-constraints");
		addAckermannFunctionConstraints(formula, constraintsList,
				functionInstances, instanceParameters);
		Formula ackermannConstraints;

        System.out.println("   Ackermann: ImpliesFormula");
		if (constraintsList.size() > 0) {
			if (constraintsList.size() == 1)
				ackermannConstraints = constraintsList.iterator().next();
			else
			{
				ackermannConstraints = new AndFormula(constraintsList);
			}
			formula = new ImpliesFormula(ackermannConstraints, formula);
		}

        System.out.println("   Ackermann: uninterpretedPredicatesToAuxiliaryVariables");
		constraintsList = new ArrayList<Formula>();

		// System.out.println("Applying Ackermann reduction to remove uninterpreted-predicates...");
		Map<String, List<PropositionalVariable>> predicateInstances = new HashMap<String, List<PropositionalVariable>>();
		Map<PropositionalVariable, List<DomainTerm>> instanceParametersPredicates = new HashMap<PropositionalVariable, List<DomainTerm>>();
		formula.uninterpretedPredicatesToAuxiliaryVariables(formula,
				predicateInstances, instanceParametersPredicates, noDependenceVars);

        System.out.println("   Ackermann: addAckermannPredicateConstraints");
		addAckermannPredicateConstraints(formula, constraints,
				predicateInstances, instanceParametersPredicates);
		if (constraintsList.size() > 0) {
			if (constraintsList.size() == 1)
				ackermannConstraints = constraintsList.iterator().next();
			else
				ackermannConstraints = new AndFormula(constraintsList);
			formula = new ImpliesFormula(ackermannConstraints, formula);
		}
		

        System.out.println("   Ackermann: removeall at last");
		//noDependenceVars.removeAll(currentDependenceArrayVariables); // parameter changed (?)
		noDependenceVars.removeAll(currentUninterpretedFunctions);		
	
		return formula;
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
					constraints.add(new ImpliesFormula(parametersEquivalities,
							new PropositionalEq(predicateEq, true)));

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

		for (Map.Entry<String, List<DomainVariable>> entry : functionInstances
				.entrySet()) {

			List<DomainVariable> instances = entry.getValue();

			for (int i = 0; i < instances.size(); i++)
				for (int j = (i + 1); j < instances.size(); j++) {
					// System.out.println(""+instances.get(i).getVarName()+" with "+instances.get(j).getVarName());

					List<DomainTerm> params1 = instanceParameters.get(instances.get(i));
					List<DomainTerm> params2 = instanceParameters.get(instances.get(j));

					List<Formula> parametersEq = new ArrayList<Formula>();
					for (int k = 0; k < params1.size(); k++) {
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
					
//					if (parametersEq.size() > 1)
//						parametersEquivalities = new AndFormula(parametersEq);
//					else
//						parametersEquivalities = parametersEq.iterator().next();

					List<DomainTerm> functionEq = new ArrayList<DomainTerm>();
					functionEq.add(instances.get(i));
					functionEq.add(instances.get(j));
					constraints.add(
					        new ImpliesFormula(parametersEquivalities,
					                new DomainEq(functionEq, true)));

				}
		}
	}
}
