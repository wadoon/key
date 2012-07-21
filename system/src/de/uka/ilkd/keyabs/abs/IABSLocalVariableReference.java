package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.logic.op.IProgramVariable;

public interface IABSLocalVariableReference extends IABSLocationReference {

    IProgramVariable getProgramVariable();
    
}
