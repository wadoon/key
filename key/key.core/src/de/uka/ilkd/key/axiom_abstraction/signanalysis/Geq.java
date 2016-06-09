package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import org.key_project.common.core.logic.Name;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * The Geq element of the sign lattice, representing
 * all positive integers and zero.
 * 
 * @author Dominic Scheurer
 */
public class Geq extends SignAnalysisDomainElem {

   private static final Geq INSTANCE = new Geq();
   
   private Geq() {}
   
   public static Geq getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("geq");
   }

   @Override
   public JavaDLTerm getDefiningAxiom(JavaDLTerm varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().geq(varOrConst, tb.zero());
   }

}
