package de.uka.ilkd.key.testgeneration.xmlparser.junitparser;

import java.util.LinkedList;
import java.util.List;

/**
 * Represents a very simple view of an Object instance, based on the metadata available in the XML
 * document.
 * 
 * @author christopher
 */
public class ObjectInstance {

    /**
     * The static type of this object.
     */
    private String type;

    /**
     * The name of this object.
     */
    private String name;

    /**
     * Indicates whether this object is declared final or not.
     */
    private boolean isFinal = false;

    /**
     * Arguments to the constructor of this object
     */
    private List<ObjectInstance> constructorArguments = new LinkedList<ObjectInstance>();

    /**
     * @return the type
     */
    public String getType() {

        return type;
    }

    /**
     * @param type
     *            the type to set
     */
    public void setType(String type) {

        this.type = type;
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
     * @return the isFinal
     */
    public boolean isFinal() {

        return isFinal;
    }

    /**
     * @param isFinal
     *            the isFinal to set
     */
    public void setFinal(boolean isFinal) {

        this.isFinal = isFinal;
    }

    /**
     * @return the constructorArguments
     */
    public List<ObjectInstance> getConstructorArguments() {

        return constructorArguments;
    }

    /**
     * @param constructorArguments
     *            the constructorArguments to set
     */
    public void addConstructorArgument(ObjectInstance argument) {

        constructorArguments.add(argument);
    }
}
