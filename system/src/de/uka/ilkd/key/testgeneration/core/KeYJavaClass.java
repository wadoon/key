package de.uka.ilkd.key.testgeneration.core;

import java.io.File;
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
     * The package declaration for this class.
     */
    private final String packageDeclaration;

    /**
     * The identifier for this class.
     */
    private final String name;

    /**
     * The {@link KeYJavaType} instance for this class
     */
    private final KeYJavaType type;

    /**
     * A reference to the actual source file on disc, whose public class this
     * instance represents.
     */
    File source;

    /**
     * Maps the name of a method to its corresponding {@link KeYJavaMethod}
     * instance.
     */
    private final HashMap<String, KeYJavaMethod> methods;

    KeYJavaClass(String packageDeclaration, String name, KeYJavaType type,
            HashMap<String, KeYJavaMethod> methodMappings, File source) {
        this.packageDeclaration = packageDeclaration;
        this.name = name;
        this.type = type;
        this.methods = methodMappings;
        this.source = source;
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
        return name;
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
        return packageDeclaration;
    }
}