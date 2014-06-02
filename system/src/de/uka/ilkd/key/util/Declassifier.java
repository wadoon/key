/**
 * 
 */
package de.uka.ilkd.key.util;

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
   
   public final ImmutableList<Term> declassifications;
   
   /**
    * @param declassification
    */
   public Declassifier(ImmutableList<Term> declassification) {
      super();
      this.declassifications = declassification;
   }
   
   
   private Declassifier() {
      this.declassifications=ImmutableSLList.<Term>nil();
   }

   public String toString() {
      return declassifications + "";
   }
}
