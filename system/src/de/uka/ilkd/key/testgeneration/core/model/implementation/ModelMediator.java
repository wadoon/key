package de.uka.ilkd.key.testgeneration.core.model.implementation;

import java.util.LinkedList;

import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYJavaClass;
import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYJavaMethod;

/**
 * This bucket class carries data needed for context resolution in a single
 * model generation session.
 * 
 * @author christopher
 * 
 */
public class ModelMediator {

    /**
     * The Java class for which we are currently in the process of generating
     * test cases.
     */
    KeYJavaClass mainClass;

    /**
     * The method for which we are generating testcases. Must be a member of
     * ModelMediator#mainClass.
     */
    KeYJavaMethod method;

    /**
     * Method parameters for the method we are currently generating a model for.
     */
    LinkedList<String> methodParameterNames = new LinkedList<String>();

    /**
     * @return the methodParameterNames
     */
    public LinkedList<String> getMethodParameterNames() {
        return methodParameterNames;
    }

    /**
     * @param methodParameterNames
     *            the methodParameterNames to set
     */
    public void setMethodParameterNames(LinkedList<String> methodParameterNames) {
        this.methodParameterNames = methodParameterNames;
    }

    /**
     * @return the mainClass
     */
    public KeYJavaClass getMainClass() {
        return mainClass;
    }

    /**
     * @param mainClass
     *            the mainClass to set
     */
    public void setMainClass(KeYJavaClass mainClass) {
        this.mainClass = mainClass;
    }

    /**
     * @return the method
     */
    public KeYJavaMethod getMethod() {
        return method;
    }

    /**
     * @param method
     *            the method to set
     */
    public void setMethod(KeYJavaMethod method) {
        this.method = method;
    }
}
