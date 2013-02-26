package de.uka.ilkd.key.testgeneration.core;

import java.util.HashMap;
import java.util.Set;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;

/**
 * Instances of this class represent an abstract view of a Java class,
 * encapsulating essential information related to test case generation.
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
    private final HashMap<String, KeYJavaMethod> methods = new HashMap<String, KeYJavaMethod>();

    KeYJavaClass(KeYJavaType type) {
        this.type = type;
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

    /**
     * @return the name
     */
    public String getName() {
        return type.getName();
    }

    /**
     * @return the type
     */
    public KeYJavaType getType() {
        return type;
    }

    /**
     * @return the packageDeclaration
     */
    public String getPackageDeclaration() {
        return type.createPackagePrefix().toString();
    }

    /**
     * Add a method for this class. Package access due to encapsulation concerns
     * (probably an antipattern).
     * 
     * @param methodName
     * @param method
     */
    void addMethodMapping(String methodName, KeYJavaMethod method) {

        methods.put(methodName, method);
    }
}