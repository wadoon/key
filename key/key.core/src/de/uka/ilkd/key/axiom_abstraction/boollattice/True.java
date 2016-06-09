package de.uka.ilkd.key.axiom_abstraction.boollattice;

import org.key_project.common.core.logic.Name;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * The True element of the boolean lattice, representing
 * exactly the boolean true.
 * 
 * @author Dominic Scheurer
 */
public class True extends BooleanDomainElem {

   private static final True INSTANCE = new True();
   
   private True() {}
   
   public static True getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("true");
   }

   @Override
   public JavaDLTerm getDefiningAxiom(JavaDLTerm varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();      
      return tb.equals(varOrConst, tb.tt());
   }

}
