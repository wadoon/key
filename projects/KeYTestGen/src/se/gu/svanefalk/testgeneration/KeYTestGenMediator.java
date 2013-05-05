package se.gu.svanefalk.testgeneration;

import java.util.LinkedList;

import se.gu.svanefalk.testgeneration.core.classabstraction.KeYJavaClass;

/**
 * Bucket class meant to carry shared data around in a single KeYTestGen
 * session.
 * 
 * @author christopher
 * 
 */
public class KeYTestGenMediator {

    /**
     * The Java class for which test cases are currently being generated.
     */
    KeYJavaClass mainClass;

    /**
     * Method parameters for a given instance
     */
    LinkedList<String> methodParameterNames = new LinkedList<String>();

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
    public void setMainClass(final KeYJavaClass mainClass) {
        this.mainClass = mainClass;
    }
}
