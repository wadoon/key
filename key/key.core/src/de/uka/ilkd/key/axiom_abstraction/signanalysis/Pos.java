package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import org.key_project.common.core.logic.Name;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * The Pos element of the sign lattice, representing
 * all strictly positive numbers.
 * 
 * @author Dominic Scheurer
 */
public class Pos extends SignAnalysisDomainElem {

   private static final Pos INSTANCE = new Pos();
   
   private Pos() {}
   
   public static Pos getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("pos");
   }

   @Override
   public JavaDLTerm getDefiningAxiom(JavaDLTerm varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().gt(varOrConst, tb.zero());
   }

}
