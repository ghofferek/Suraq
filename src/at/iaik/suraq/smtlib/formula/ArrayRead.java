/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.exceptions.WrongNumberOfParametersException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.HashTagContainer;
import at.iaik.suraq.util.Util;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayRead extends DomainTerm {

    /**
     * 
     */
    private static final long serialVersionUID = -2549087326175334824L;

    /**
     * The array variable that is read.
     */
    private final ArrayTerm arrayTerm;

    /**
     * The index from which is read.
     */
    private final DomainTerm indexTerm;

    /**
     * Constructs a new <code>ArrayRead</code>.
     * 
     * @param arrayTerm
     *            the variable that is read
     * @param index
     *            the index from which is read.
     */
    private ArrayRead(ArrayTerm arrayTerm, DomainTerm index) {
        super();
        this.arrayTerm = arrayTerm;
        this.indexTerm = index;
    }

    public static ArrayRead create(ArrayTerm arrayTerm, DomainTerm index) {
        return (ArrayRead) FormulaCache.domainTerm.put(new ArrayRead(arrayTerm,
                index));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#isEvar(java.util.Collection)
     */
    @Override
    public boolean isEvar(Collection<DomainVariable> uVars) {
        // not applicable for ArrayRead.
        return false;
    }

    /**
     * Returns the index from which is read.
     * 
     * @return the index from which is read.
     */
    public DomainTerm getIndexTerm() {
        return indexTerm;
    }

    /**
     * Returns the array variable from which is read.
     * 
     * @return the array variable from which is read.
     */
    public ArrayTerm getArrayTerm() {
        return arrayTerm;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public DomainTerm deepTermCopy() {
        return this; // experimental
        // return new ArrayRead((ArrayTerm) arrayTerm.deepTermCopy(),
        // indexTerm.deepTermCopy());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getArrayVariables()
     */
    @Override
    public void getArrayVariables(Set<ArrayVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        arrayTerm.getArrayVariables(result, done);
        indexTerm.getArrayVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getDomainVariables()
     */
    @Override
    public void getDomainVariables(Set<DomainVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        arrayTerm.getDomainVariables(result, done);
        indexTerm.getDomainVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getPropositionalVariables()
     */
    @Override
    public void getPropositionalVariables(Set<PropositionalVariable> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        arrayTerm.getPropositionalVariables(result, done);
        indexTerm.getPropositionalVariables(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacroNames()
     */
    @Override
    public void getFunctionMacroNames(Set<String> result, Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        arrayTerm.getFunctionMacroNames(result, done);
        indexTerm.getFunctionMacroNames(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getFunctionMacros()
     */
    @Override
    public void getFunctionMacros(Set<FunctionMacro> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        arrayTerm.getFunctionMacros(result, done);
        indexTerm.getFunctionMacros(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctionNames()
     */
    @Override
    public void getUninterpretedFunctionNames(Set<String> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        arrayTerm.getUninterpretedFunctionNames(result, done);
        indexTerm.getUninterpretedFunctionNames(result, done);
        done.add(this);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof ArrayRead))
            return false;

        if (this.hashCode() != obj.hashCode())
            return false;

        return arrayTerm.equals(((ArrayRead) obj).arrayTerm)
                && indexTerm.equals(((ArrayRead) obj).indexTerm);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return arrayTerm.hashCode() * 31 + indexTerm.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        if (!(arrayTerm instanceof ArrayVariable))
            throw new SuraqException(
                    "Encountered array-read from non-variable array term while computing index set.");
        Set<DomainTerm> result = new HashSet<DomainTerm>();
        result.add(indexTerm);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteTerm(Map)
     */
    @Override
    public Term substituteTerm(Map<Token, ? extends Term> paramMap,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.containsKey(this)) {
            assert (done.get(this) != null);
            assert (done.get(this) instanceof Term);
            return (Term) done.get(this);
        }
        Term result = ArrayRead.create(
                (ArrayTerm) arrayTerm.substituteTerm(paramMap, done),
                (DomainTerm) indexTerm.substituteTerm(paramMap, done));
        assert (result != null);
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        SExpression[] expr = new SExpression[3];
        expr[0] = SExpressionConstants.SELECT;
        expr[1] = arrayTerm.toSmtlibV2();
        expr[2] = indexTerm.toSmtlibV2();
        return new SExpression(expr);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayPropertiesToFiniteConjunctions(java.util.Set)
     */
    @Override
    public Term arrayPropertiesToFiniteConjunctionsTerm(Set<DomainTerm> indexSet) {
        ArrayTerm arrayTerm = (ArrayTerm) this.arrayTerm
                .arrayPropertiesToFiniteConjunctionsTerm(indexSet);
        DomainTerm indexTerm = (DomainTerm) this.indexTerm
                .arrayPropertiesToFiniteConjunctionsTerm(indexSet);
        return ArrayRead.create(arrayTerm, indexTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayEqualitiesTerm()
     */
    @Override
    public Term removeArrayEqualitiesTerm() {
        ArrayTerm arrayTerm = (ArrayTerm) this.arrayTerm
                .removeArrayEqualitiesTerm();
        DomainTerm indexTerm = (DomainTerm) this.indexTerm
                .removeArrayEqualitiesTerm();
        return ArrayRead.create(arrayTerm, indexTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        ArrayTerm arrayTerm = this.arrayTerm;
        DomainTerm indexTerm = this.indexTerm;

        if (arrayTerm instanceof ArrayWrite)
            arrayTerm = ((ArrayWrite) arrayTerm).applyWriteAxiom(
                    topLevelFormula, constraints, noDependenceVars);
        else
            arrayTerm = (ArrayTerm) arrayTerm.removeArrayWritesTerm(
                    topLevelFormula, constraints, noDependenceVars);

        indexTerm = (DomainTerm) indexTerm.removeArrayWritesTerm(
                topLevelFormula, constraints, noDependenceVars);

        return ArrayRead.create(arrayTerm, indexTerm);
    }

    /**
     * Returns an <code>UninterpretedFunctionInstance</code> that is
     * "equivalent" to this <code>ArrayRead</code>.
     * 
     * @return an <code>UninterpretedFunctionInstance</code> that is
     *         "equivalent" to this <code>ArrayRead</code>.
     */
    public UninterpretedFunctionInstance toUninterpretedFunctionInstance(
            Set<Token> noDependenceVars) {
        try {
            // Complex array terms should have been removed before.
            assert (arrayTerm instanceof ArrayVariable);
            // String functionName = arrayTerm.toSmtlibV2().toString()
            // .replaceAll("\\W", "");
            String functionName = ((ArrayVariable) arrayTerm).getVarName();

            DomainTerm term = indexTerm;

            if (term instanceof ArrayRead)
                term = ((ArrayRead) term)
                        .toUninterpretedFunctionInstance(noDependenceVars);
            else
                term = (DomainTerm) term
                        .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);

            // Check if the arrayTerm contained any noDependenceVars.
            // This is conservative and might not be complete (i.e., may
            // result unnecessary unrealizability), but
            // in practice, array reads should only occur on primitive
            // array expressions, so this should not be a "real" problem.
            if (Util.termContainsAny(arrayTerm, noDependenceVars))
                noDependenceVars.add(Token.generate(functionName));

            return UninterpretedFunctionInstance.create(UninterpretedFunction
                    .create(functionName, 1, SExpressionConstants.VALUE_TYPE),
                    term);
        } catch (WrongNumberOfParametersException exc) {
            throw new RuntimeException(
                    "Could not replace array-reads with uninterpreted functions",
                    exc);
        }
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(
            Set<Token> noDependenceVars) {
        throw new RuntimeException(
                "arrayReadsToUninterpretedFunctions cannot be called on an ArrayWrite.\nUse toUninterpretedFunctionInstance instead.");
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getUninterpretedFunctions()
     */
    @Override
    public void getUninterpretedFunctions(Set<UninterpretedFunction> result,
            Set<SMTLibObject> done) {
        if (done.contains(this))
            return;
        arrayTerm.getUninterpretedFunctions(result, done);
        indexTerm.getUninterpretedFunctions(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Term substituteUninterpretedFunctionTerm(
            Map<Token, UninterpretedFunction> substitutions) {
        ArrayTerm arrayTerm = (ArrayTerm) this.arrayTerm
                .substituteUninterpretedFunctionTerm(substitutions);
        DomainTerm indexTerm = (DomainTerm) this.indexTerm
                .substituteUninterpretedFunctionTerm(substitutions);
        return ArrayRead.create(arrayTerm, indexTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#flatten()
     */
    @Override
    public Term flatten() {
        return ArrayRead.create((ArrayTerm) arrayTerm.flatten(),
                (DomainTerm) indexTerm.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(Formula,
     *      java.util.Set, Set)
     */
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        if (this.indexTerm instanceof DomainVariable)
            return this; // This read is already simple.

        DomainTerm oldIndexTerm = this.indexTerm;
        DomainTerm indexTerm = DomainVariable.create(Util.freshVarNameCached(
                topLevelFormula, "read"));

        List<DomainTerm> list = new ArrayList<DomainTerm>();
        list.add(indexTerm);
        list.add(oldIndexTerm);
        constraints.add(DomainEq.create(list, true));

        // Check if the arrayTerm contained any noDependenceVars.
        // This is conservative and might not be complete (i.e., may
        // result unnecessary unrealizability), but
        // in practice, array reads should only occur on primitive
        // array expressions, so this should not be a "real" problem.
        if (Util.termContainsAny(arrayTerm, noDependenceVars))
            noDependenceVars.add(Token.generate(((DomainVariable) indexTerm)
                    .getVarName()));

        return ArrayRead.create(this.arrayTerm, indexTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public DomainTerm uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) {
     * 
     * return new ArrayRead(
     * arrayTerm.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars),
     * indexTerm.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars));
     * 
     * }
     */

    /**
     * Returns the elements assert-partition.
     * 
     * @return assert-partition of the element.
     */
    @Override
    public Set<Integer> getPartitionsFromSymbols() {
        Set<Integer> partitions = arrayTerm.getPartitionsFromSymbols();
        partitions.addAll(indexTerm.getPartitionsFromSymbols());

        return partitions;
    }

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Term uninterpretedPredicatesToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<PropositionalVariable>> predicateInstances,
            Map<PropositionalVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        throw new RuntimeException(
                "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an ArrayRead.");

        /*
         * arrayTerm.uninterpretedPredicatesToAuxiliaryVariables(
         * topLeveFormula, predicateInstances, instanceParameters,
         * noDependenceVars);
         * indexTerm.uninterpretedPredicatesToAuxiliaryVariables(
         * topLeveFormula, predicateInstances, instanceParameters,
         * noDependenceVars);
         */
    }

    /**
     * @see at.iaik.suraq.formula.Term#uninterpretedFunctionsToAuxiliaryVariables(at.iaik.suraq.formula.Formula,
     *      java.util.Map, java.util.Map)
     */
    @Override
    public Term uninterpretedFunctionsToAuxiliaryVariablesTerm(
            Formula topLeveFormula,
            Map<String, List<DomainVariable>> functionInstances,
            Map<DomainVariable, List<DomainTerm>> instanceParameters,
            Set<Token> noDependenceVars) {

        throw new RuntimeException(
                "uninterpretedFunctionsToAuxiliaryVariables cannot be called on an ArrayRead.");
        /*
         * arrayTerm.uninterpretedFunctionsToAuxiliaryVariables( topLeveFormula,
         * functionInstances, instanceParameters, noDependenceVars);
         * indexTerm.uninterpretedFunctionsToAuxiliaryVariables( topLeveFormula,
         * functionInstances, instanceParameters, noDependenceVars);
         */
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public DomainTerm uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars) {
        return ArrayRead.create(
                arrayTerm.uninterpretedFunctionsBackToArrayReads(arrayVars),
                indexTerm.uninterpretedFunctionsBackToArrayReads(arrayVars));
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeDomainITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.List)
     */
    @Override
    public ArrayRead removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        ArrayTerm newArrayTerm = arrayTerm.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        DomainTerm newIndexTerm = indexTerm.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        return ArrayRead.create(newArrayTerm, newIndexTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.DomainTerm#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public DomainTerm removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        ArrayTerm newArrayTerm = arrayTerm.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        DomainTerm newIndexTerm = indexTerm.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        return ArrayRead.create(newArrayTerm, newIndexTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#writeOut(java.io.BufferedWriter,
     *      at.iaik.suraq.util.HashTagContainer, boolean)
     */
    @Override
    public void writeOut(BufferedWriter writer, HashTagContainer tagContainer)
            throws IOException {
        throw new NotImplementedException();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.write("(");
        writer.write(SExpressionConstants.SELECT.toString());
        writer.write(" ");
        arrayTerm.writeTo(writer);
        writer.write(" ");
        indexTerm.writeTo(writer);
        writer.write(")");
    }
}
