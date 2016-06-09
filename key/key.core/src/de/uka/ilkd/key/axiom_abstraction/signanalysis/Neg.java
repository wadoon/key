package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import org.key_project.common.core.logic.Name;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * The Neg element of the sign lattice, representing
 * all strictly negative integers.
 * 
 * @author Dominic Scheurer
 */
public class Neg extends SignAnalysisDomainElem {

   private static final Neg INSTANCE = new Neg();
   
   private Neg() {}
   
   public static Neg getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("neg");
   }

   @Override
   public JavaDLTerm getDefiningAxiom(JavaDLTerm varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().lt(varOrConst, tb.zero());
   }

}
