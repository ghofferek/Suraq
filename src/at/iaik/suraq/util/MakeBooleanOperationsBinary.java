/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.List;

import at.iaik.suraq.parser.SExpParser;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class MakeBooleanOperationsBinary implements Runnable {

    private final String[] args;

    public MakeBooleanOperationsBinary(String[] args) {
        this.args = args;
    }

    /**
     * @param args
     *            input file, output file
     */
    public static void main(String[] args) {
        try {
            MakeBooleanOperationsBinary obj = new MakeBooleanOperationsBinary(
                    args);
            obj.run();
            System.exit(0);
        } catch (Throwable exc) {
            if (exc.getMessage() != null)
                System.err.println(exc.getMessage());
            exc.printStackTrace();
            System.exit(-1);
        }

    }

    /**
     * 
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {
        try {
            if (args == null) {
                throw new RuntimeException(
                        "Expect 2 arguments: Input file, output file.");
            }
            if (args.length < 2) {
                throw new RuntimeException(
                        "Expect 2 arguments: Input file, output file.");
            }
            SExpParser parser = new SExpParser(new File(args[0]));
            parser.parse();

            SExpression root = parser.getRootExpr();
            SExpression result = makeBooleanOperationsBinary(root);

            File outputFile = new File(args[1]);
            FileWriter fwriter = new FileWriter(outputFile);
            BufferedWriter writer = new BufferedWriter(fwriter);
            result.writeTo(writer);
            writer.close();
            fwriter.close();
            return;

        } catch (Throwable exc) {
            throw new RuntimeException(exc.getMessage(), exc);
        }
    }

    /**
     * @param expression
     * @return
     */
    private SExpression makeBooleanOperationsBinary(SExpression expression) {

        if (expression instanceof Token)
            return expression;

        if (expression.getChildren().isEmpty())
            return expression;

        if (expression.getChildren().get(0).equals(SExpressionConstants.AND)
                || expression.getChildren().get(0)
                        .equals(SExpressionConstants.OR)
                || expression.getChildren().get(0)
                        .equals(SExpressionConstants.XOR)) {
            Token operator = (Token) expression.getChildren().get(0);
            if (expression.getChildren().size() > 3) {
                SExpression tmp = new SExpression(operator,
                        makeBooleanOperationsBinary(expression.getChildren()
                                .get(1)),
                        makeBooleanOperationsBinary(expression.getChildren()
                                .get(2)));
                for (int count = 3; count < expression.getChildren().size(); count++) {
                    tmp = new SExpression(operator, tmp,
                            makeBooleanOperationsBinary(expression
                                    .getChildren().get(count)));
                }
                return tmp;
            }
        }

        List<SExpression> newChildren = new ArrayList<SExpression>(expression
                .getChildren().size());
        for (SExpression child : expression.getChildren())
            newChildren.add(makeBooleanOperationsBinary(child));
        return new SExpression(newChildren);
    }
}
