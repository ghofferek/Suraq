/**
 * Author: Ashutosh Gupta <agupta@ist.ac.at>
 */
package at.iaik.suraq.resProof;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Lit {
    int l;

    public Lit( int i, boolean b){ l = (i << 1) | (b?1:0); }

    public int var(){ return l>>1; }
    public boolean isPos(){ return  (l & 0x1) == 1; }
    public int negate(){ return  (l ^ 0x1); }
    public Lit negLit(){ return new Lit( var(), !isPos() ); }

    @Override public boolean equals(Object obj){
        if (obj == null) return false;  
        if (getClass() != obj.getClass()) return false;  
        return this.l == ((Lit)obj).l; 
    }

    @Override public int hashCode() { return l; }

    public String toString(){
        if( (l & 1) == 0 ) 
            return "~"+(l>>1);
        else
            return Integer.toString( l>>1 );
    }


}
