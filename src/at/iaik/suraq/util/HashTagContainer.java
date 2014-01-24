/**
 * Author: Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 */
package at.iaik.suraq.util;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import at.iaik.suraq.smtlib.formula.DomainTerm;
import at.iaik.suraq.smtlib.formula.Formula;

/**
 * @author Georg Hofferek <georg.hofferek@iaik.tugraz.at>
 * 
 */
public class HashTagContainer {

    /**
     * Map for formulas to hashTags
     */
    private final Map<Formula, Integer> formulaMap;

    /**
     * Map for terms to hashTags
     */
    private final Map<DomainTerm, Integer> termMap;

    /**
     * the next hashTag to be used.
     */
    private int nextHashTag = 1;

    public HashTagContainer() {
        formulaMap = new HashMap<Formula, Integer>();
        termMap = new HashMap<DomainTerm, Integer>();
    }

    /**
     * Puts the given <code>formula</code> into the internal map, with a new
     * hashTag. If it is already there, the intermal map remains unchanged and
     * the existing tag is returned.
     * 
     * @param formula
     * @return the hashTag of the formula
     */
    public int put(Formula formula) {
        Integer tag = formulaMap.get(formula);
        if (tag != null)
            return tag;
        formulaMap.put(formula, nextHashTag);
        return nextHashTag++;
    }

    /**
     * Puts the given <code>term</code> into the internal map, with a new
     * hashTag. If it is already there, the intermal map remains unchanged and
     * the existing tag is returned.
     * 
     * @param term
     * @return the hashTag of the formula
     */
    public int put(DomainTerm term) {
        Integer tag = termMap.get(term);
        if (tag != null)
            return tag;
        termMap.put(term, nextHashTag);
        return nextHashTag++;
    }

    /**
     * 
     * @param formula
     * @return the tag for <code>formula</code>
     */
    public int get(Formula formula) {
        Integer tag = formulaMap.get(formula);
        if (tag == null)
            return 0;
        return tag;
    }

    /**
     * 
     * @param formula
     * @return the tag for <code>formula</code>
     */
    public int get(DomainTerm term) {
        Integer tag = termMap.get(term);
        if (tag == null)
            return 0;
        return tag;
    }

    /**
     * 
     * @param formula
     * @return <code>true</code> iff there is already a tag for
     *         <code>formula</code>.
     */
    public boolean contains(Formula formula) {
        return formulaMap.get(formula) == null;
    }

    /**
     * 
     * @param term
     * @return <code>true</code> iff there is already a tag for
     *         <code>term</code>.
     */
    public boolean contains(DomainTerm term) {
        return termMap.get(term) == null;
    }

    /**
     * 
     * @param formula
     * @param writer
     * 
     * @throws IOException
     */
    public void handle(Formula formula, BufferedWriter writer)
            throws IOException {
        Integer hashTag = formulaMap.get(formula);
        if (hashTag != null) {
            assert (hashTag != null);
            writer.append('#');
            writer.append(hashTag.toString());
            writer.append(' ');
        } else {
            formulaMap.put(formula, nextHashTag);
            hashTag = nextHashTag++;
            writer.append("#");
            writer.append(hashTag.toString());
            writer.append(':');
            formula.writeOut(writer, this, false);
        }
    }

}
