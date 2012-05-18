/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;

import org.junit.Assert;

public class Clause extends HashSet<Lit> {

    /**
     * 
     */

    private static final long serialVersionUID = 1L;
    public static boolean chkNegLit = false;

    public Clause() {
        super();
    }

    public Clause(Collection<Lit> cl) {
        super();
        addAllLit(cl);
    }

    public Clause(Collection<Lit> clLeft, Collection<Lit> clRight, int pivot) {
        super();
        addAllLit( clLeft );
        rmLit(pivot, true);
        if( contains(pivot, false) ){
            addAllLit( clRight );
        }else{
            addAllLit( clRight );
            rmLit(pivot, false);
        }
    }

    public void addAllLit(Collection<Lit> cl) {
        Iterator<Lit> itr = cl.iterator();
        while (itr.hasNext())
            addLit(itr.next());
    }

    public void addLit(Lit l) {
        if(chkNegLit) 
            Assert.assertTrue("~l and l in a clause", !this.contains(l.negLit()));
        this.add(l);
    }

    public void rmLit(Lit l) {
        this.remove(l);
    }

    public void rmLit(int a, boolean b) {
        this.remove(new Lit(a, b));
    }

    public boolean contains(int a, boolean b) {
        return this.contains(new Lit(a, b));
    }

}
