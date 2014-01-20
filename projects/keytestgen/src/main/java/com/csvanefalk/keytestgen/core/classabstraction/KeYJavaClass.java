package com.csvanefalk.keytestgen.core.classabstraction;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

import java.util.HashMap;
import java.util.Set;

/**
 * Instances of this class represent an abstract view of a Java class,
 * encapsulating essential information related to test case generation.
 *
 * @author christopher
 */
public final class KeYJavaClass {

    private final KeYEnvironment<CustomConsoleUserInterface> environment;

    private final InitConfig initConfig;

    /**
     * Maps the name of a method to its corresponding {@link KeYJavaMethod}
     * instance.
     */
    private final HashMap<String, KeYJavaMethod> methods = new HashMap<String, KeYJavaMethod>();

    /**
     * The {@link KeYJavaType} instance for this class
     */
    private final KeYJavaType type;

    KeYJavaClass(final KeYJavaType type, final InitConfig initConfig) {
        this.type = type;
        environment = null;
        this.initConfig = environment.getInitConfig();
    }

    KeYJavaClass(final KeYJavaType type, final KeYEnvironment<CustomConsoleUserInterface> environment) {
        this.type = type;
        this.environment = environment;
        initConfig = environment.getInitConfig();
    }

    /**
     * Add a method for this class. Package access due to encapsulation concerns
     * (probably an antipattern).
     *
     * @param methodName
     * @param method
     */
    void addMethodMapping(final String methodName, final KeYJavaMethod method) {

        methods.put(methodName, method);
    }

    public KeYEnvironment<CustomConsoleUserInterface> getEnvironment() {
        return environment;
    }

    /**
     * Retrieves the {@link KeYJavaMethod} instance corresponding to the
     * provided name, or <code>code</code> if such a method cannot be found.
     *
     * @param name the name of the method
     * @return the {@link KeYJavaType} instance for the method
     */
    public KeYJavaMethod getMethod(final String name) {

        return methods.get(name);
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
     * @return the name
     */
    public String getName() {
        return type.getName();
    }

    /**
     * @return the packageDeclaration
     */
    public String getPackageDeclaration() {
        PackageReference pr = type.createPackagePrefix();
        return pr != null ? pr.toString() : null;
    }

    /**
     * @return the type
     */
    public KeYJavaType getType() {
        return type;
    }
}