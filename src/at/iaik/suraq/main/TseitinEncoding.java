package at.iaik.suraq.main;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.parser.TseitinParser;
import at.iaik.suraq.smtlib.formula.AndFormula;
import at.iaik.suraq.smtlib.formula.Formula;
import at.iaik.suraq.smtlib.formula.OrFormula;
import at.iaik.suraq.smtlib.formula.PropositionalVariable;
import at.iaik.suraq.util.DebugHelper;
import at.iaik.suraq.util.Timer;
import at.iaik.suraq.util.Util;

/**
 * TseitinEncoding extracted to this method. It is not globally used in this
 * project yet. But this TseitinEncoding should also work. Used in: - QBFTest -
 * ONLY Before QBFEncoding in class Suraq
 * 
 * @author chillebold
 * 
 */
public class TseitinEncoding {
    protected Map<PropositionalVariable, Formula> tseitinEncoding = new HashMap<PropositionalVariable, Formula>();

    public Formula performTseitinEncodingWithoutZ3(Formula formula) {
        Formula formula2 = formula.deepFormulaCopy();

        Timer timer = new Timer();
        timer.reset();
        timer.start();

        List<OrFormula> clauses = new ArrayList<OrFormula>();
        Map<PropositionalVariable, Formula> encoding = new HashMap<PropositionalVariable, Formula>();

        // the following code also changes the formula
        // GH 2013-05-02: Not sure where this is used,
        // just putting -1 for the partition parameters,
        // as this is probably not used anywhere anyway.
        Formula tseitinVar = formula.tseitinEncode(clauses, encoding, -1);
        assert (Util.isLiteral(tseitinVar));
        tseitinEncoding.putAll(encoding);
        if (tseitinVar instanceof PropositionalVariable)
            tseitinEncoding.put((PropositionalVariable) tseitinVar, formula);

        List<Formula> disjuncts = new ArrayList<Formula>();
        disjuncts.add(tseitinVar);
        clauses.add(OrFormula.generate(disjuncts));
        Formula encodedFormula = AndFormula.generate(clauses);

        timer.end();
        DebugHelper.getInstance().formulaToFile(encodedFormula,
                "debug-tseitin-encoding.txt");

        System.out.println("      test if tseitin encoding is correct...");
        assert (TseitinParser.checkFormulaImplication(encodedFormula, formula2));
        System.out.println("      ...test finished");

        System.out.println(" Done. (" + timer + ")");
        return encodedFormula;
    }

    public Set<PropositionalVariable> getPropositionalVariables() {
        return tseitinEncoding.keySet();
    }
}
