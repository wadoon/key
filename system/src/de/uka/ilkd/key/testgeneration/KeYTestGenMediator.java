package de.uka.ilkd.key.testgeneration;

import de.uka.ilkd.key.testgeneration.keyinterface.KeYJavaClass;

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
