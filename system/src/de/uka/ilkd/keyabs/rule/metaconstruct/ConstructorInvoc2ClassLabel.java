package de.uka.ilkd.keyabs.rule.metaconstruct;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.keyabs.abs.ABSServices;

public class ConstructorInvoc2ClassLabel extends AbstractTermTransformer {

    public ConstructorInvoc2ClassLabel() {
        super(new Name("#constrInvoc2ClassLabel"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, IServices services) {

        ABSServices serv = (ABSServices) services;

        ProgramElementName className = (ProgramElementName) svInst.getInstantiation((SchemaVariable) term.sub(0).op());
        
        
        if (className == null) {
            throw new RuntimeException("No instantiation for class name");
        }

        final Function cLabel = serv.getProgramInfo().getClassLabelFor(className);
        
        if (cLabel == null) {
            throw new IllegalStateException("There is no class of name " + cLabel);
        }
        
        return TB.func(cLabel);
    }

}
