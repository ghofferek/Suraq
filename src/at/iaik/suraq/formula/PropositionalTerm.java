/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.formula;

/**
 * A propositional term. I.e., either a propositional constant or a
 * propositional variable, or a propositional if-then-else construct.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class PropositionalTerm extends Term implements Formula {
    // just for type safety. No actual methods on this level.
}
