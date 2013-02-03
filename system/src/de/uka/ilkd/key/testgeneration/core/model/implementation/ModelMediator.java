package de.uka.ilkd.key.testgeneration.core.model.implementation;

import java.util.LinkedList;

import de.uka.ilkd.key.testgeneration.core.keyinterface.KeYJavaClass;

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
}
