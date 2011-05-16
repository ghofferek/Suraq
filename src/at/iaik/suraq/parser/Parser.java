/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import at.iaik.suraq.exceptions.ParseError;

/**
 * An abstract super class of parsers.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public abstract class Parser {

    /**
     * Indicates whether or not parsing of the source associated with this
     * parser has already completed successfully.
     */
    protected boolean parsingSuccessfull = false;

    /**
     * @return <code>true</code> if this parser completed parsing successfully,
     *         <code>false</code> otherwise.
     */
    public boolean wasParsingSuccessfull() {
        return parsingSuccessfull;
    }

    /**
     * Performs the actual parsing.
     * 
     * @throws ParseError
     *             if parsing fails.
     */
    public abstract void parse() throws ParseError;

}
