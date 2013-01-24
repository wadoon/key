package de.uka.ilkd.key.testgeneration.model.implementation;

/**
 * Implementors of this interface represent primitive or reference values on the
 * heap.
 * 
 * @author christopher
 */
public interface IHeapValue extends IHeapObject {

    public void setValue(IHeapValue value);

    @Override
    public IHeapValue getValue();
}
