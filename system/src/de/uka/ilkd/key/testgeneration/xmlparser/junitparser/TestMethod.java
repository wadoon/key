package de.uka.ilkd.key.testgeneration.xmlparser.junitparser;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.statement.Assert;

/**
 * This bean represents a simple view of a JUnit test method, i.e. a method annotated with @Test.
 * 
 * @author christopher
 */
public class TestMethod {

    /**
     * The name of this testMethod.
     */
    String name;

    /**
     * Object instances declared in this particular method, represented by {@link ObjectInstance}.
     */
    private final List<ObjectInstance> objectInstances = new LinkedList<ObjectInstance>();

    /**
     * The oracle for this method, ie the set of calls to methods of {@link Assert} determining
     * whether the test case succeeded or failed.
     */
    private String oracle;

    /**
     * @return the objectInstances
     */
    public List<ObjectInstance> getObjectInstances() {

        return objectInstances;
    }

    public void addObjectInstance(ObjectInstance instance) {

        objectInstances.add(instance);
    }

    /**
     * @return the name
     */
    public String getName() {

        return name;
    }

    /**
     * @param name
     *            the name to set
     */
    public void setName(String name) {

        this.name = name;
    }

    /**
     * @return the oracle
     */
    public String getOracle() {

        return oracle;
    }

    /**
     * @param oracle
     *            the oracle to set
     */
    public void setOracle(String oracle) {

        this.oracle = oracle;
    }
}
