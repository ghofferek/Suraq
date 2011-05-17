/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

/**
 * Represents an if-then-else-style formula.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class IteFormula extends BooleanCombinationFormula {

    private final Formula condition;

    private final Formula thenBranch;

    private final Formula elseBranche;
}
