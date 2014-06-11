/**
 * 
 */
package de.uka.ilkd.key.util;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Term;

/**
 * wrapping information flow security
 * first, we just use it to contain declassification information 
 * @author Huy Do
 *
 */
public class DelimitedRelease {
   public static final DelimitedRelease EMPTY_DECLASSIFIER = new DelimitedRelease();
   
   //represent conditional delimited release. Map(A,B) represents: if formula A holds then expression B is allowed to be leaked
   //private final Map<Term, Term> declassifications;
   public final ImmutableList<Term> conditions;
   public final ImmutableList<Term> leaks;
   
   /**
    * @param declassification
    */
   public DelimitedRelease(ImmutableList<Term> conditions, ImmutableList<Term> leaks) {
      super();
      this.conditions = conditions;
      this.leaks = leaks;
   }
      
   private DelimitedRelease() {
      this.conditions = ImmutableSLList.<Term>nil();
      this.leaks = ImmutableSLList.<Term>nil();
   }   
  

   public String toString() {
      return "if " + conditions + " then leaks " + leaks;
   }
}
