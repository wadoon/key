package de.uka.ilkd.key.testgeneration.model;

/**
 * Represents a general variable on the program heap.
 * 
 * @author christopher
 */
public interface IModelObject {

    String getName();

    String getType();

    Object getValue();
}
