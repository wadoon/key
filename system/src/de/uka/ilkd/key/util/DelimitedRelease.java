/**
 * 
 */
package de.uka.ilkd.key.util;

import java.util.LinkedList;
import java.util.List;

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
   public static final DelimitedRelease EMPTY_DelimitedRelease = new DelimitedRelease();
   
   //represent conditional delimited release. Map(A,B) represents: if formula A holds then expression B is allowed to be leaked
   //private final Map<Term, Term> declassifications;
   public final ImmutableList<Term> conditions; //list of escape conditions
   public final ImmutableList<Term> escapeHatches;  //list of 
   
   public final ImmutableList<Term> lowVars;
   /**
    * @param conditions, escapeHatches
    */
   public DelimitedRelease(ImmutableList<Term> conditions, ImmutableList<Term> escapeHatches) {
      super();
      this.conditions = conditions;
      this.escapeHatches = escapeHatches;
      this.lowVars = ImmutableSLList.<Term>nil();
   }
      
   private DelimitedRelease() {
      this.conditions = ImmutableSLList.<Term>nil();
      this.escapeHatches = ImmutableSLList.<Term>nil();
      this.lowVars = ImmutableSLList.<Term>nil();
   } 
   
   

   /**
    * @param conditions
    * @param escapeHatches
    * @param lowVars
    */
   public DelimitedRelease(ImmutableList<Term> conditions,
         ImmutableList<Term> escapeHatches, ImmutableList<Term> lowVars) {
      super();
      this.conditions = conditions;
      this.escapeHatches = escapeHatches;
      this.lowVars = lowVars;
   }

   public String toString() {
      return "if " + conditions + " then leaks " + escapeHatches + " to " + lowVars; 
   }
   
   
}
