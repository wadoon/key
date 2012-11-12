package de.uka.ilkd.key.testgeneration.model.modelgeneration.implementation;

/**
 * Represents a general variable on the program heap. Such a variable is
 * identified by its name, type, value, and parent object.
 * 
 * @author christopher
 */
public interface IModelVariable {
    
    String getName();

    String getType();

    Object getValue();

    IModelVariable getParent();
}
