/**
 * Author: Christoph Hillebold <c.hillebold@student.tugraz.at>
 */
package at.iaik.suraq.main;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.DomainEq;
import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.DomainVariable;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.ImpliesFormula;
import at.iaik.suraq.smtlib.formula.PropositionalEq;
import at.iaik.suraq.smtlib.formula.PropositionalTerm;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.smtlib.formula.UninterpretedFunction;
import at.iaik.suraq.smtlib.formula.UninterpretedFunctionInstance;
import at.iaik.suraq.smtlib.formula.UninterpretedPredicateInstance;
import at.iaik.suraq.util.DebugHelper;

/**
 * This class is used to perform Ackermann's reduction to a given formula.
 * 
 * @author Hillebold Christoph
 * 
 */
public class Ackermann {

    // these flags activate or deactivate Ackermann's reduction
    // you can separately deactivate it on predicates and functions.
    private static boolean _isActive = false;
    private static boolean _isPredicateActive = true;
    private static boolean _isFunctionActive = true;
    // active debug writes out some files to see what's going on
    private static boolean _debug = true;

    /**
     * performs the Ackermann's reduction and removes Functions and Predicates
     * This method adds noDependenceVars (DomainVars) to the
     * noDependenceVars-List and removes Functions and Predicates from the
     * noDependenceVars-List
     * 
     * @param topLevelFormula
     *            formula to work with
     * @param noDependenceVars
     * @return
     */
    public Formula performAckermann(Formula topLevelFormula,
            Set<Token> noDependenceVars) {
        // For Debugging issues you can deactivate the Ackermann's reduction by
        // calling Ackermann.setActive(false);
        if (!Ackermann._isActive) {
            System.out
                    .println("* INFO: Didn't perform Ackermann, because it was deactivated.");
            return topLevelFormula;
        }

        // Get all UF-Names and store them to a set of Tokens.
        System.out.println("   Ackermann: getUninterpretedFunctionNames()");
        Set<Token> currentUninterpretedFunctions = new HashSet<Token>();

        UninterpretedPredicateInstance.method = Ackermann._isPredicateActive;
        UninterpretedFunctionInstance.method = Ackermann._isFunctionActive;
        Set<String> ufs = new HashSet<String>();
        topLevelFormula.getUninterpretedFunctionNames(ufs,
                new HashSet<SMTLibObject>());
        for (String var : ufs)
            currentUninterpretedFunctions.add(Token.generate(var));
        UninterpretedPredicateInstance.method = true;
        UninterpretedFunctionInstance.method = true;
        // this adds UFs as well as UPs... as expected

        // //////////////////////////////////////////////////////////
        // Substitute UF by Variables
        if (Ackermann._isFunctionActive) {
            System.out
                    .println("   Ackermann: uninterpretedFunctionsToAuxiliaryVariables(...)");
            Map<String, List<DomainVariable>> functionInstances = new HashMap<String, List<DomainVariable>>();
            Map<DomainVariable, List<DomainTerm>> instanceParameters = new HashMap<DomainVariable, List<DomainTerm>>();

            if (Ackermann._debug)
                DebugHelper.getInstance().formulaToFile(topLevelFormula,
                        "./debug_aux_func_before.txt");
            topLevelFormula = topLevelFormula
                    .uninterpretedFunctionsToAuxiliaryVariables(
                            topLevelFormula, functionInstances,
                            instanceParameters, noDependenceVars);
            if (Ackermann._debug)
                DebugHelper.getInstance().formulaToFile(topLevelFormula,
                        "./debug_aux_func_after.txt");

            // Add Constraints for these UFs
            System.out.println("   Ackermann: add UF-constraints(...)");
            List<Formula> constraintsList = new ArrayList<Formula>();
            addAckermannFunctionConstraints(topLevelFormula, constraintsList,
                    functionInstances, instanceParameters);
            System.out.println("   Ackermann: added UF-constraints(...): cnt="
                    + constraintsList.size());

            // Generate the Implies formula FC => !flat
            System.out.println("   Ackermann: ImpliesFormula(...)");
            if (constraintsList.size() > 0) {
                Formula ackermannConstraints = (constraintsList.size() == 1) ? constraintsList
                        .iterator().next() : AndFormula
                        .generate(constraintsList);
                topLevelFormula = ImpliesFormula.create(ackermannConstraints,
                        topLevelFormula);
            } else {
                System.out
                        .println("   Ackermann: There are no FunctionConstraints.");
            }

        } else {
            System.err
                    .println(" *** Warning: Ackermann didn't perform on Functions (disabled)");
        }

        // //////////////////////////////////////////////////////////

        if (Ackermann._isPredicateActive) {
            // Init for UP
            // constraintsList = new ArrayList<Formula>();

            // substitute UP by Variables
            System.out
                    .println("   Ackermann: uninterpretedPredicatesToAuxiliaryVariables(...)");
            Map<String, List<PropositionalVariable>> predicateInstances = new HashMap<String, List<PropositionalVariable>>();
            Map<PropositionalVariable, List<DomainTerm>> instanceParametersPredicates = new HashMap<PropositionalVariable, List<DomainTerm>>();

            if (Ackermann._debug)
                DebugHelper.getInstance().formulaToFile(topLevelFormula,
                        "./debug_aux_pred_before.txt");
            topLevelFormula = topLevelFormula
                    .uninterpretedPredicatesToAuxiliaryVariables(
                            topLevelFormula, predicateInstances,
                            instanceParametersPredicates, noDependenceVars);
            if (Ackermann._debug)
                DebugHelper.getInstance().formulaToFile(topLevelFormula,
                        "./debug_aux_pred_after.txt");

            System.out.println("   Ackermann: predicateInstances.size: "
                    + predicateInstances.size());
            System.out
                    .println("   Ackermann: instanceParametersPredicates.size: "
                            + instanceParametersPredicates.size());
            // Add Constraints for these UPs
            System.out
                    .println("   Ackermann: addAckermannPredicateConstraints(...)");

            // HashSet<Formula> constraints = new HashSet<Formula>();
            List<Formula> constraintsList = new ArrayList<Formula>();
            addAckermannPredicateConstraints(topLevelFormula, constraintsList,
                    predicateInstances, instanceParametersPredicates);

            // Generate the Implies formula FC => !flat
            if (constraintsList.size() > 0) {
                Formula ackermannConstraints = (constraintsList.size() == 1) ? constraintsList
                        .iterator().next() : AndFormula
                        .generate(constraintsList);
                topLevelFormula = ImpliesFormula.create(ackermannConstraints,
                        topLevelFormula);
            } else {
                System.out
                        .println("   Ackermann: There are no PredicateConstraints.");
            }
        } else {
            System.err
                    .println(" *** Warning: Ackermann didn't perform on Predicates (disabled)");
        }

        // debug check:
        if (Ackermann._isPredicateActive && Ackermann._isFunctionActive) {

            Set<UninterpretedFunction> ufs2 = new HashSet<UninterpretedFunction>();
            topLevelFormula.getUninterpretedFunctions(ufs2,
                    new HashSet<SMTLibObject>());
            System.out.println("Count of UF: " + ufs2.size());
            assert (ufs2.isEmpty());
        }

        // //////////////////////////////////////////////////////////

        // remove all UF and UP (?)
        System.out.println("   Ackermann: noDependenceVars.removeall(UF)");
        System.out.println("    Anzahl der Variablen bevor dem Entfernen: "
                + noDependenceVars.size());
        System.out.println("    Entfernt werden sollten "
                + currentUninterpretedFunctions.size() + "Variablen");
        noDependenceVars.removeAll(currentUninterpretedFunctions);
        // may remove too much (functions and predicates) if one is deactivated
        System.out.println("    Anzahl der Variablen nach dem Entfernen: "
                + noDependenceVars.size());

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
            List<Formula> constraints,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters) {

        for (Map.Entry<String, List<PropositionalVariable>> entry : predicateInstances
                .entrySet()) {

            List<PropositionalVariable> instances = entry.getValue();

            for (int i = 0; i < instances.size(); i++)
                for (int j = (i + 1); j < instances.size(); j++) {

                    List<DomainTerm> params1 = instanceParameters.get(instances
                            .get(i));
                    List<DomainTerm> params2 = instanceParameters.get(instances
                            .get(j));

                    List<Formula> parametersEq = new ArrayList<Formula>();
                    for (int k = 0; k < params1.size(); k++) {

                        // Compute functional consistency constraints
                        List<DomainTerm> list = new ArrayList<DomainTerm>();
                        list.add(params1.get(k));
                        list.add(params2.get(k));
                        parametersEq.add(DomainEq.create(list, true));

                    }
                    Formula parametersEquivalities;
                    if (parametersEq.size() > 1)
                        parametersEquivalities = AndFormula
                                .generate(parametersEq);
                    else
                        parametersEquivalities = parametersEq.iterator().next();

                    List<PropositionalTerm> predicateEq = new ArrayList<PropositionalTerm>();
                    predicateEq.add(instances.get(i));
                    predicateEq.add(instances.get(j));
                    constraints.add(ImpliesFormula.create(
                            parametersEquivalities,
                            PropositionalEq.create(predicateEq, true)));

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

                    List<DomainTerm> params1 = instanceParameters.get(instances
                            .get(i));
                    List<DomainTerm> params2 = instanceParameters.get(instances
                            .get(j));

                    List<Formula> parametersEq = new ArrayList<Formula>();
                    for (int k = 0; k < params1.size(); k++) {
                        // System.out.println("   "+t1.get(k)+"^"+t2.get(k));

                        // Compute functional consistency constraints
                        List<DomainTerm> list = new ArrayList<DomainTerm>();
                        list.add(params1.get(k));
                        list.add(params2.get(k));
                        parametersEq.add(DomainEq.create(list, true));
                    }
                    Formula parametersEquivalities = (parametersEq.size() > 1) ? AndFormula
                            .generate(parametersEq) : parametersEq.iterator()
                            .next();

                    List<DomainTerm> functionEq = new ArrayList<DomainTerm>();
                    functionEq.add(instances.get(i));
                    functionEq.add(instances.get(j));
                    constraints.add(ImpliesFormula.create(
                            parametersEquivalities,
                            DomainEq.create(functionEq, true)));

                }
        }
    }

    public static boolean isFunctionActive() {
        return Ackermann._isFunctionActive;
    }

    public static void setFunctionActive(boolean _isFunctionActive) {
        Ackermann._isFunctionActive = _isFunctionActive;
    }

    public static boolean isPredicateActive() {
        return Ackermann._isPredicateActive;
    }

    public static void setPredicateActive(boolean _isPredicateActive) {
        Ackermann._isPredicateActive = _isPredicateActive;
    }

    public static void setActive(boolean isActive) {
        Ackermann._isActive = isActive;
    }

    public static boolean isActive() {
        return Ackermann._isActive;
    }

    public static void setDebug(boolean isDebugEnabled) {
        Ackermann._debug = isDebugEnabled;
    }

    public static boolean isDebug() {
        return Ackermann._debug;
    }

}
