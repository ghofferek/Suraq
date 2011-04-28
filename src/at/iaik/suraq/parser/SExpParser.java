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

import at.iaik.suraq.sexp.SExpression;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 *         A simple parser for LISP-like S-expressions.
 */
public class SExpParser {

    /**
     * The source string to be parsed into an S-expression.
     */
    private final List<String> sourceLines;

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
     * Parses the input specified at construction time.
     * 
     * @return a list of s-expressions corresponding to the input.
     */
    public List<SExpression> parse() {
        List<SExpression> list = new ArrayList<SExpression>();

        return list;
    }

}
