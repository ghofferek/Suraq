/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.parser;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import at.iaik.suraq.exceptions.ParseError;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.Token;

/**
 * A simple parser for LISP-like S-expressions.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
public class SExpParser {

    /**
     * The current state of this parser. If <code>true</code> it's processing a
     * comment.
     */
    private boolean commentState = false;

    /**
     * Indicates whether or not the parser is processing a quoted token at the
     * moment.
     */
    private boolean quotedToken = false;

    /**
     * The source string to be parsed into an S-expression.
     */
    private final List<String> sourceLines;

    /**
     * The current expression the parser is working on.
     */
    private SExpression currentExpr = null;

    /**
     * The current line number, or 0 if none.
     */
    private int currentLineNumber = 0;

    /**
     * The current line.
     */
    private String currentLine = null;

    /**
     * The current column number.
     */
    private int currentColumnNumber = 0;

    /**
     * The string (buffer) representation of the current token.
     */
    private StringBuffer currentToken = null;

    /**
     * The (implicit) root of the parse tree.
     */
    protected SExpression rootExpr = null;

    /**
     * A stack of parent expressions of the current expression.
     */
    private Stack<SExpression> parentExpr;

    /**
     * Creates a parser to parse the given string.
     * 
     * @param source
     *            the string to parse
     */
    public SExpParser(String source) {
        String[] stringArray = source.split("\n");
        sourceLines = new ArrayList<String>();
        for (String string : stringArray) {
            sourceLines.add(string);
        }
    }

    /**
     * Constructs a new <code>SExpParser</code>, to parse the given file. The
     * file is read during construction of this parser object.
     * 
     * @param sourceFile
     *            the file to read.
     * @throws IOException
     *             if an I/O exception occurs during reading the file
     * @throws FileNotFoundException
     *             if the given file cannot be found/read.
     */
    public SExpParser(File sourceFile) throws IOException,
            FileNotFoundException {
        FileReader reader = new FileReader(sourceFile);
        BufferedReader bufferedReader = new BufferedReader(reader);
        sourceLines = new ArrayList<String>();

        String currentLine = bufferedReader.readLine();
        while (currentLine != null) {
            sourceLines.add(currentLine);
            currentLine = bufferedReader.readLine();
        }

        bufferedReader.close();
        reader.close();
    }

    /**
     * @return an array containing all the source lines.
     */
    public String[] getSourceLines() {
        return (String[]) sourceLines.toArray();
    }

    /**
     * Parses the input specified at construction time. The parsed s-expression
     * is stored in <code>rootExpr</code>.
     * 
     * @throws ParseError
     *             if parsing fails.
     */
    public void parse() throws ParseError {
        rootExpr = new SExpression();
        parentExpr = new Stack<SExpression>();
        parentExpr.push(rootExpr);
        currentExpr = null;

        while (++currentLineNumber <= sourceLines.size()) {
            currentLine = sourceLines.get(currentLineNumber - 1);
            currentColumnNumber = 0;
            commentState = false;

            if (quotedToken) {
                assert (currentToken != null);
                currentToken.append('\n');
            }

            for (char character : currentLine.toCharArray()) {
                currentColumnNumber++;

                if (character == ';') // start of a comment
                    commentState = true;
                if (commentState) // ignore rest of line
                    continue;

                if (character == '(') { // start of a subexpression
                    if (currentExpr != null)
                        parentExpr.push(currentExpr);
                    currentExpr = new SExpression();
                }

                if (character == ')') { // end of a subexpression
                    if (currentExpr == null || parentExpr.size() < 1)
                        throw new ParseError(currentLineNumber,
                                currentColumnNumber, currentLine,
                                "Unmatched \")\".");
                    else {
                        parentExpr.peek().addChild(currentExpr);
                        if (parentExpr.size() == 1) { // only the root
                                                      // expression is left.
                            currentExpr = null;
                        } else {
                            currentExpr = parentExpr.pop();
                        }
                    }
                }

                if (character == ' ' || character == '\t' || character == '\n'
                        || character == '\r') { // whitespace
                    if (currentToken == null) // no current token, just ignore
                                              // the whitespace
                        continue;
                    else {
                        if (quotedToken) // we are in a quoted token. Whitespace
                                         // belongs to token.
                            currentToken.append(character);
                        else
                            // this whitespace ends the token. Store it.
                            storeToken();
                    }

                }

                if (character == '"') {
                    if (currentToken == null) { // no current token --> start
                                                // new quoted token
                        quotedToken = true;
                        currentToken = new StringBuffer();
                        currentToken.append(character);
                    } else {
                        if (quotedToken) {
                            if (currentToken.charAt(currentToken.length() - 1) == '\\')
                                // an escaped ". Just append it.
                                currentToken.append(character);
                            else { // the end of the quoted token. Store it.
                                currentToken.append(character);
                                storeToken();
                                quotedToken = false;
                            }
                        } else { // found a " in a non-quoted token. --> Error
                            throw new ParseError(currentLineNumber,
                                    currentColumnNumber, currentLine,
                                    "Unexpected '\"'.");
                        }
                    }
                }

                // We are dealing with an "ordinary" character. So either just
                // append it to the current token or start a new token.
                if (currentToken == null)
                    currentToken = new StringBuffer();
                currentToken.append(character);
            }
        }
    }

    /**
     * Stores the current token in the parse tree.
     */
    private void storeToken() {
        if (currentExpr != null)
            currentExpr.addChild(new Token(currentToken));
        else {
            assert (parentExpr.size() == 1);
            parentExpr.peek().addChild(new Token(currentToken));
        }
        currentToken = null;
    }

}
