package de.uka.ilkd.key.testgeneration.keyinterface;

import java.util.HashMap;
import java.util.Set;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;

/**
 * This class encapsulates information related to a Java class, to the extent
 * such information is needed for test case generation.
 * 
 * @author christopher
 */
public final class KeYJavaClass {

    /**
     * The {@link KeYJavaType} instance for this class
     */
    private final KeYJavaType type;

    /**
     * Maps the name of a method to its corresponding {@link KeYJavaMethod}
     * instance.
     */
    private final HashMap<String, KeYJavaMethod> methods;

    KeYJavaClass(KeYJavaType type, HashMap<String, KeYJavaMethod> methodMappings) {
        this.type = type;
        this.methods = methodMappings;
    }

    /**
     * Get the names of all methods declared in this class
     * 
     * @return a {@link Set} with method names
     */
    public Set<String> getMethods() {

        return methods.keySet();
    }

    /**
     * Retrieves the {@link KeYJavaMethod} instance corresponding to the
     * provided name, or <code>code</code> if such a method cannot be found.
     * 
     * @param name
     *            the name of the method
     * @return the {@link KeYJavaType} instance for the method
     */
    public KeYJavaMethod getMethod(String name) {

        return methods.get(name);
    }
}