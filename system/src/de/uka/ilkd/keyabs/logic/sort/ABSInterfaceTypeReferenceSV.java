package de.uka.ilkd.keyabs.logic.sort;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.ABSTypeReference;
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;

public class ABSInterfaceTypeReferenceSV extends ABSTypeReferenceSV {
   
    public ABSInterfaceTypeReferenceSV() {
        super(new Name("ABSInterfaceTypeRef"));
    }

    @Override
    public boolean canStandFor(ProgramElement check, ExecutionContext ec,
            ABSServices services) {
        return super.canStandFor(check, ec, services) && ((ABSTypeReference)check).getKeYJavaType().getJavaType() instanceof ABSInterfaceType;
    }

}
