package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import java.util.Iterator;
import java.util.NoSuchElementException;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import org.jetbrains.annotations.NotNull;

/**
 * A lattice for sign analysis of integers.
 *
 * @author Dominic Scheurer
 */
public class SignAnalysisLattice extends AbstractDomainLattice {

   /**
    * All elements of this abstract domain.
    */
   public static final AbstractDomainElement[] ABSTRACT_DOMAIN_ELEMS = {
      Bottom.getInstance(),
      Neg.getInstance(),
      Zero.getInstance(),
      Pos.getInstance(),
      Leq.getInstance(),
      Geq.getInstance(),
      Top.getInstance()
   };

   /**
    * The singleton instance of this lattice.
    */
   private static final SignAnalysisLattice INSTANCE = new SignAnalysisLattice();

   /**
    * Private constructor (singleton!).
    */
   private SignAnalysisLattice() {}

   /**
    * @return The singleton instance of this lattice.
    */
   public static SignAnalysisLattice getInstance() {
      return INSTANCE;
   }

   @Override
   public AbstractDomainElement join(AbstractDomainElement elem1,
         AbstractDomainElement elem2) {

      if (!(elem1 instanceof SignAnalysisDomainElem) ||
          !(elem2 instanceof SignAnalysisDomainElem)) {
         throw new IllegalArgumentException("Expected arguments of the abstract domain of sign analysis.");
      }

      SignAnalysisDomainElem a = (SignAnalysisDomainElem) elem1;
      SignAnalysisDomainElem b = (SignAnalysisDomainElem) elem2;

      if (a.isTop() || b.isTop()) {
         return Top.getInstance();
      }

      if (a.isLeq()) {
         if (b.isGeq() || b.isPos()) {
            return Top.getInstance();
         } else {
            return Leq.getInstance();
         }
      }

      if (a.isGeq()) {
         if (b.isLeq() || b.isNeg()) {
            return Top.getInstance();
         } else {
            return Geq.getInstance();
         }
      }

      if (b.isLeq()) {
         if (a.isGeq() || a.isPos()) {
            return Top.getInstance();
         } else {
            return Leq.getInstance();
         }
      }

      if (b.isGeq()) {
         if (a.isLeq() || a.isNeg()) {
            return Top.getInstance();
         } else {
            return Geq.getInstance();
         }
      }

      if (a.isNeg()) {
         if (b.isZero()) {
            return Leq.getInstance();
         } else if (b.isPos()) {
            return Top.getInstance();
         } else {
            return Neg.getInstance();
         }
      }

      if (a.isZero()) {
         if (b.isNeg()) {
            return Leq.getInstance();
         } else if (b.isPos()) {
            return Geq.getInstance();
         } else {
            return Zero.getInstance();
         }
      }

      if (a.isPos()) {
         if (b.isZero()) {
            return Geq.getInstance();
         } else if (b.isNeg()) {
            return Top.getInstance();
         } else {
            return Pos.getInstance();
         }
      }

      assert(a.isBottom()) : "Bug in sign lattice implementation.";
      return b;
   }

   @Override
   public Iterator<AbstractDomainElement> iterator() {
      return getAbstractDomainElementIterator(ABSTRACT_DOMAIN_ELEMS);
   }
}
