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
public class Declassifier {
   public static final Declassifier EMPTY_DECLASSIFIER = new Declassifier();
   
   //represent conditional delimited release. Map(A,B) represents: if formula A holds then expression B is allowed to be leaked
   //private final Map<Term, Term> declassifications;
   public final ImmutableList<Term> conditions;
   public final ImmutableList<Term> leaks;
   
   /**
    * @param declassification
    */
   public Declassifier(ImmutableList<Term> conditions, ImmutableList<Term> leaks) {
      super();
      this.conditions = conditions;
      this.leaks = leaks;
   }
      
   private Declassifier() {
      this.conditions = ImmutableSLList.<Term>nil();
      this.leaks = ImmutableSLList.<Term>nil();
   }   
  

   public String toString() {
      return "if " + conditions + " then leaks " + leaks;
   }
}
