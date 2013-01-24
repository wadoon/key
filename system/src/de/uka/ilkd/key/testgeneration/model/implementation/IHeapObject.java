package de.uka.ilkd.key.testgeneration.model.implementation;

import de.uka.ilkd.key.testgeneration.model.IModelObject;

/**
 * A heap object corresponds to a unique object on the program heap during
 * runtime.
 * 
 * @author christopher
 */
public interface IHeapObject extends IModelObject {

    public String getIdentifier();
}
