package de.uka.ilkd.key.axiom_abstraction.boollattice;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Named;
import org.key_project.common.core.logic.op.LogicVariable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * The Bottom element of the boolean lattice, representing
 * no boolean at all.
 * 
 * @author Dominic Scheurer
 */
public class Bottom extends BooleanDomainElem {

   private static final Bottom INSTANCE = new Bottom();
   
   private Bottom() {}
   
   public static Bottom getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("bottom");
   }

   @Override
   public Term getDefiningAxiom(Term varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();
      
      final Name freshVarName = new Name(tb.newName(varOrConst.sort()));
      services.getNamespaces().variables().add(new Named() {
         @Override
         public Name name() {
            return freshVarName;
         }
      });
      LogicVariable freshVar = new LogicVariable(freshVarName, varOrConst.sort());
      
      Term axiom = tb.equals(varOrConst, tb.var(freshVar));
      axiom = tb.not(axiom);
      axiom = tb.all(freshVar, axiom);
      
      return axiom;
   }

}
