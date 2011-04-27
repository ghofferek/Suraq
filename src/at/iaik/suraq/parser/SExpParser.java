/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 *
 * A simple parser for LISP-like S-expressions.
 */
public class SExpParser {
	
	/**
	 * The source string to be parsed into an S-expression.
	 */
	private final String sourceString;

	/**
	 * Creates a parser to parse the given string.
	 * @param source the string to parse
	 */
	public SExpParser(String source) {
		sourceString = source;
	}


	/**
	 * @return the <code>sourceString</code>
	 */
	public String getSourceString() {
		return sourceString;
	}

}
