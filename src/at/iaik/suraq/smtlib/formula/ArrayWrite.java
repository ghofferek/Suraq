/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.smtlib.formula;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import at.iaik.suraq.exceptions.SuraqException;
import at.iaik.suraq.sexp.SExpression;
import at.iaik.suraq.sexp.SExpressionConstants;
import at.iaik.suraq.sexp.Token;
import at.iaik.suraq.smtlib.SMTLibObject;
import at.iaik.suraq.util.FormulaCache;
import at.iaik.suraq.util.Util;

/**
 * An array write expression.
 * 
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class ArrayWrite extends ArrayTerm {

    /**
     * 
     */
    private static final long serialVersionUID = -2087596963751666011L;

    /**
     * The array to which this expression writes.
     */
    private final ArrayTerm arrayTerm;

    /**
     * The index to which this expression writes.
     */
    private final DomainTerm indexTerm;

    /**
     * The value that is written.
     */
    private final DomainTerm valueTerm;

    /**
     * Constructs a new <code>ArrayWrite</code>.
     * 
     * @param arrayTerm
     *            the array to which is written.
     * @param indexTerm
     *            the index to which is written.
     * @param valueTerm
     *            the value being written.
     */
    private ArrayWrite(ArrayTerm arrayTerm, DomainTerm indexTerm,
            DomainTerm valueTerm) {
        this.arrayTerm = arrayTerm;
        this.indexTerm = indexTerm;
        this.valueTerm = valueTerm;
    }

    public static ArrayWrite create(ArrayTerm arrayTerm, DomainTerm indexTerm,
            DomainTerm valueTerm) {
        return (ArrayWrite) FormulaCache.term.put(new ArrayWrite(arrayTerm,
                indexTerm, valueTerm));
    }

    /**
     * Returns the array to which is written.
     * 
     * @return the <code>arrayTerm</code>
     */
    public ArrayTerm getArrayTerm() {
        return arrayTerm;
    }

    /**
     * Returns the index to which is written.
     * 
     * @return the <code>indexTerm</code>
     */
    public DomainTerm getIndexTerm() {
        return indexTerm;
    }

    /**
     * Returns the value being written.
     * 
     * @return the <code>valueTerm</code>
     */
    public DomainTerm getValueTerm() {
        return valueTerm;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#deepTermCopy()
     */
    @Override
    public Term deepTermCopy() {
        return this;
        // return new ArrayWrite((ArrayTerm) arrayTerm.deepTermCopy(),
        // indexTerm.deepTermCopy(), valueTerm.deepTermCopy());
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
        valueTerm.getArrayVariables(result, done);
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
        valueTerm.getDomainVariables(result, done);
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
        valueTerm.getPropositionalVariables(result, done);
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
        valueTerm.getFunctionMacroNames(result, done);
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
        valueTerm.getFunctionMacros(result, done);
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
        valueTerm.getUninterpretedFunctionNames(result, done);
        done.add(this);
    }

    /**
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!(obj instanceof ArrayWrite))
            return false;

        if (this.hashCode() != obj.hashCode())
            return false;

        return ((ArrayWrite) obj).arrayTerm.equals(arrayTerm)
                && ((ArrayWrite) obj).indexTerm.equals(indexTerm)
                && ((ArrayWrite) obj).valueTerm.equals(valueTerm);
    }

    /**
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return arrayTerm.hashCode() * 31 * 31 + indexTerm.hashCode() * 31
                + valueTerm.hashCode();
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#getIndexSet()
     */
    @Override
    public Set<DomainTerm> getIndexSet() throws SuraqException {
        throw new SuraqException(
                "Encountered array write while computing index set.");
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
        Term result = ArrayWrite.create(
                (ArrayTerm) arrayTerm.substituteTerm(paramMap, done),
                (DomainTerm) indexTerm.substituteTerm(paramMap, done),
                (DomainTerm) valueTerm.substituteTerm(paramMap, done));
        assert (result != null);
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#toSmtlibV2()
     */
    @Override
    public SExpression toSmtlibV2() {
        SExpression[] expr = new SExpression[4];
        expr[0] = SExpressionConstants.STORE;
        expr[1] = arrayTerm.toSmtlibV2();
        expr[2] = indexTerm.toSmtlibV2();
        expr[3] = valueTerm.toSmtlibV2();
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
        DomainTerm valueTerm = (DomainTerm) this.valueTerm
                .arrayPropertiesToFiniteConjunctionsTerm(indexSet);
        return ArrayWrite.create(arrayTerm, indexTerm, valueTerm);
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
        DomainTerm valueTerm = (DomainTerm) this.valueTerm
                .removeArrayEqualitiesTerm();
        return ArrayWrite.create(arrayTerm, indexTerm, valueTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#removeArrayWrites(at.iaik.suraq.smtlib.formula.Formula)
     */
    @Override
    public Term removeArrayWritesTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        throw new RuntimeException(
                "removeArrayWrites cannot be called on an ArrayWrite.\nUse applyWriteAxiom instead.");

    }

    /**
     * Applies the write axiom to this <code>ArrayWrite</code> term. I.e.,
     * returns a (fresh) <code>ArrayVariable</code> to be used instead of this
     * term.
     * 
     * @param topLevelFormula
     *            the top-level formula (w.r.t. which fresh names are selected)
     * @param constraints
     *            A set of formulas to which the constraints of the write
     *            axiom's application will be added.
     * @return an <code>ArrayVariable</code> with a fresh name.
     */
    public ArrayVariable applyWriteAxiom(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {

        ArrayVariable result;
        DomainTerm index;
        DomainTerm value;

        // First, recursively remove writes from sub-parts
        if (arrayTerm instanceof ArrayWrite)
            result = ((ArrayWrite) arrayTerm).applyWriteAxiom(topLevelFormula,
                    constraints, noDependenceVars);
        else {
            assert (arrayTerm instanceof ArrayVariable);
            result = (ArrayVariable) arrayTerm;
        }

        index = indexTerm;
        index = (DomainTerm) index.removeArrayWritesTerm(topLevelFormula,
                constraints, noDependenceVars);
        if (!(index instanceof DomainVariable)) {
            DomainVariable simpleIndex = DomainVariable.create(Util
                    .freshVarNameCached(topLevelFormula, "read"));
            List<DomainTerm> terms = new ArrayList<DomainTerm>();
            terms.add(simpleIndex);
            terms.add(index);
            constraints.add(DomainEq.create(terms, true));

            noDependenceVars.add(Token.generate(simpleIndex.getVarName()));
            index = simpleIndex;
        }

        value = valueTerm;
        value = (DomainTerm) value.removeArrayWritesTerm(topLevelFormula,
                constraints, noDependenceVars);

        // now apply axiom
        String oldVar = result.getVarName();
        ArrayVariable newVar = ArrayVariable.create(Util.freshVarNameCached(
                topLevelFormula, oldVar + "_store"));

        ArrayRead newRead = ArrayRead.create(newVar, index);
        newRead = (ArrayRead) newRead.makeArrayReadsSimpleTerm(topLevelFormula,
                constraints, noDependenceVars);
        value = (DomainTerm) value.makeArrayReadsSimpleTerm(topLevelFormula,
                constraints, noDependenceVars);
        Set<DomainTerm> domainTerms = new HashSet<DomainTerm>();
        domainTerms.add(newRead);
        domainTerms.add(value);
        constraints.add(DomainEq.create(domainTerms, true));

        DomainVariable newUVar = DomainVariable.create(Util.freshVarNameCached(
                topLevelFormula, "uVar"));
        domainTerms.clear();
        domainTerms.add(index);
        domainTerms.add(newUVar);
        Formula indexGuard = DomainEq.create(domainTerms, false);

        domainTerms.clear();
        domainTerms.add(ArrayRead.create(newVar, newUVar));
        domainTerms.add(ArrayRead.create(result, newUVar));
        Formula valueConstraint = DomainEq.create(domainTerms, true);

        Set<DomainVariable> uVars = new HashSet<DomainVariable>();
        uVars.add(newUVar);
        try {
            constraints.add(ArrayProperty.create(uVars, indexGuard,
                    valueConstraint));
        } catch (SuraqException exc) {
            exc.printStackTrace();
            throw new RuntimeException("Could not apply write axiom.", exc);
        }

        // Make the new array a noDependenceVar
        // (store-results are "future" values, on which we should not depend.)
        noDependenceVars.add(Token.generate(newVar.getVarName()));

        return newVar;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#arrayReadsToUninterpretedFunctions()
     */
    @Override
    public Term arrayReadsToUninterpretedFunctionsTerm(
            Set<Token> noDependenceVars) {
        ArrayTerm arrayTerm = this.arrayTerm;
        DomainTerm indexTerm = this.indexTerm;
        DomainTerm valueTerm = this.valueTerm;

        arrayTerm = (ArrayTerm) arrayTerm
                .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);

        if (indexTerm instanceof ArrayRead)
            indexTerm = ((ArrayRead) indexTerm)
                    .toUninterpretedFunctionInstance(noDependenceVars);
        else
            indexTerm = (DomainTerm) indexTerm
                    .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);

        if (valueTerm instanceof ArrayRead)
            valueTerm = ((ArrayRead) valueTerm)
                    .toUninterpretedFunctionInstance(noDependenceVars);
        else
            valueTerm = (DomainTerm) valueTerm
                    .arrayReadsToUninterpretedFunctionsTerm(noDependenceVars);

        return ArrayWrite.create(arrayTerm, indexTerm, valueTerm);
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
        valueTerm.getUninterpretedFunctions(result, done);
        done.add(this);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#substituteUninterpretedFunction(Token,
     *      at.iaik.suraq.smtlib.formula.UninterpretedFunction)
     */
    @Override
    public Term substituteUninterpretedFunction(
            Map<Token, UninterpretedFunction> substitutions,
            Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null) {
            assert (done.get(this) instanceof Term);
            return (Term) done.get(this);
        }
        ArrayTerm arrayTerm = (ArrayTerm) this.arrayTerm
                .substituteUninterpretedFunction(substitutions, done);
        DomainTerm indexTerm = this.indexTerm.substituteUninterpretedFunction(
                substitutions, done);

        Term result = ArrayWrite.create(arrayTerm, indexTerm, valueTerm);
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#flatten()
     */
    @Override
    public Term flatten() {
        return ArrayWrite.create((ArrayTerm) arrayTerm.flatten(),
                (DomainTerm) indexTerm.flatten(),
                (DomainTerm) valueTerm.flatten());
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#makeArrayReadsSimple(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, Set)
     */
    @Override
    public Term makeArrayReadsSimpleTerm(Formula topLevelFormula,
            Set<Formula> constraints, Set<Token> noDependenceVars) {
        ArrayTerm arrayTerm = (ArrayTerm) this.arrayTerm
                .makeArrayReadsSimpleTerm(topLevelFormula, constraints,
                        noDependenceVars);
        DomainTerm indexTerm = (DomainTerm) this.indexTerm
                .makeArrayReadsSimpleTerm(topLevelFormula, constraints,
                        noDependenceVars);
        DomainTerm valueTerm = (DomainTerm) this.valueTerm
                .makeArrayReadsSimpleTerm(topLevelFormula, constraints,
                        noDependenceVars);

        return ArrayWrite.create(arrayTerm, indexTerm, valueTerm);

    }

    /**
     * @see at.iaik.suraq.smtlib.formula.ArrayTerm#uninterpretedPredicatesToAuxiliaryVariables(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Set)
     */
    /*
     * @Override public ArrayTerm uninterpretedPredicatesToAuxiliaryVariables(
     * Formula topLeveFormula, Set<Formula> constraints, Set<Token>
     * noDependenceVars) { return new ArrayWrite(
     * arrayTerm.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars),
     * indexTerm.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars),
     * valueTerm.uninterpretedPredicatesToAuxiliaryVariables( topLeveFormula,
     * constraints, noDependenceVars)); }
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
        partitions.addAll(valueTerm.getPartitionsFromSymbols());

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
                "uninterpretedPredicatesToAuxiliaryVariables cannot be called on an ArrayWrite.");

        /*
         * arrayTerm.uninterpretedPredicatesToAuxiliaryVariables(
         * topLeveFormula, predicateInstances, instanceParameters,
         * noDependenceVars);
         * indexTerm.uninterpretedPredicatesToAuxiliaryVariables(
         * topLeveFormula, predicateInstances, instanceParameters,
         * noDependenceVars);
         * valueTerm.uninterpretedPredicatesToAuxiliaryVariables(
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
                "uninterpretedFunctionsToAuxiliaryVariables cannot be called on an ArrayWrite.");

        /*
         * arrayTerm.uninterpretedFunctionsToAuxiliaryVariables( topLeveFormula,
         * functionInstances, instanceParameters, noDependenceVars);
         * indexTerm.uninterpretedFunctionsToAuxiliaryVariables( topLeveFormula,
         * functionInstances, instanceParameters,noDependenceVars);
         * valueTerm.uninterpretedFunctionsToAuxiliaryVariables( topLeveFormula,
         * functionInstances, instanceParameters, noDependenceVars);
         */
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.ArrayTerm#uninterpretedFunctionsBackToArrayReads(java.util.Set)
     */
    @Override
    public ArrayTerm uninterpretedFunctionsBackToArrayReads(
            Set<ArrayVariable> arrayVars, Map<SMTLibObject, SMTLibObject> done) {
        if (done.get(this) != null)
            return (ArrayTerm) done.get(this);
        ArrayTerm result = ArrayWrite.create((ArrayTerm) arrayTerm
                .uninterpretedFunctionsBackToArrayReads(arrayVars, done),
                (DomainTerm) indexTerm.uninterpretedFunctionsBackToArrayReads(
                        arrayVars, done),
                (DomainTerm) valueTerm.uninterpretedFunctionsBackToArrayReads(
                        arrayVars, done));
        done.put(this, result);
        return result;
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.ArrayTerm#removeDomainITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.List)
     */
    @Override
    public ArrayWrite removeDomainITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, List<Formula> andPreList) {
        ArrayTerm newArrayTerm = arrayTerm.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        DomainTerm newIndexTerm = indexTerm.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        DomainTerm newValueTerm = valueTerm.removeDomainITE(topLevelFormula,
                noDependenceVars, andPreList);
        return ArrayWrite.create(newArrayTerm, newIndexTerm, newValueTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.ArrayTerm#removeArrayITE(at.iaik.suraq.smtlib.formula.Formula,
     *      java.util.Set, java.util.Collection)
     */
    @Override
    public ArrayTerm removeArrayITE(Formula topLevelFormula,
            Set<Token> noDependenceVars, Collection<Formula> constraints) {
        ArrayTerm newArrayTerm = arrayTerm.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        DomainTerm newIndexTerm = indexTerm.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        DomainTerm newValueTerm = valueTerm.removeArrayITE(topLevelFormula,
                noDependenceVars, constraints);
        return ArrayWrite.create(newArrayTerm, newIndexTerm, newValueTerm);
    }

    /**
     * @see at.iaik.suraq.smtlib.formula.Term#writeTo(java.io.Writer)
     */
    @Override
    public void writeTo(Writer writer) throws IOException {
        writer.write("(");
        writer.write(SExpressionConstants.STORE.toString());
        writer.write(" ");
        arrayTerm.writeTo(writer);
        writer.write(" ");
        indexTerm.writeTo(writer);
        writer.write(" ");
        valueTerm.writeTo(writer);
        writer.write(")");
    }

}
