package de.uka.ilkd.key.testgeneration.xmlparser.junitparser;

import java.util.LinkedList;
import java.util.List;

/**
 * Represents a simple view of a JUnit test method, i.e. a method annotated with @Test.
 * 
 * @author christopher
 */
public class TestMethod {

    /**
     * Object instances declared in this particular method.
     */
    private final List<ObjectInstance> objectInstances = new LinkedList<ObjectInstance>();

    /**
     * The oracle for this method
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
}
