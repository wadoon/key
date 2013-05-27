package se.gu.svanefalk.testgeneration.core.classabstraction;

import java.util.HashMap;
import java.util.Set;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Instances of this class represent an abstract view of a Java class,
 * encapsulating essential information related to test case generation.
 * 
 * @author christopher
 */
public final class KeYJavaClass {

    /**
     * Maps the name of a method to its corresponding {@link KeYJavaMethod}
     * instance.
     */
    private final HashMap<String, KeYJavaMethod> methods = new HashMap<String, KeYJavaMethod>();

    private final InitConfig initConfig;

    private final KeYEnvironment<CustomConsoleUserInterface> environment;

    public KeYEnvironment<CustomConsoleUserInterface> getEnvironment() {
        return environment;
    }

    /**
     * The {@link KeYJavaType} instance for this class
     */
    private final KeYJavaType type;

    KeYJavaClass(final KeYJavaType type,
            KeYEnvironment<CustomConsoleUserInterface> environment) {
        this.type = type;
        this.environment = environment;
        this.initConfig = environment.getInitConfig();
    }

    KeYJavaClass(final KeYJavaType type, InitConfig initConfig) {
        this.type = type;
        this.environment = null;
        this.initConfig = environment.getInitConfig();
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

    /**
     * Retrieves the {@link KeYJavaMethod} instance corresponding to the
     * provided name, or <code>code</code> if such a method cannot be found.
     * 
     * @param name
     *            the name of the method
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
        return type.createPackagePrefix().toString();
    }

    /**
     * @return the type
     */
    public KeYJavaType getType() {
        return type;
    }
}