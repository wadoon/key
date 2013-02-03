package de.uka.ilkd.key.testgeneration.core.xmlparser.junitparser;

import java.util.LinkedList;
import java.util.List;

/**
 * Instances of this bean represent simple views of object instances.
 * 
 * @author christopher
 */
public class ObjectInstance {

    private String identifier;

    /**
     * The static type of this object.
     */
    private String type;

    /**
     * Indicates whether this object is declared final or not.
     */
    private boolean isFinal = false;

    /**
     * Arguments to the constructor of this object
     */
    private List<ObjectInstance> constructorArguments = new LinkedList<ObjectInstance>();

    /**
     * Fields of this object instance
     */
    private List<ObjectVariable> fields = new LinkedList<ObjectVariable>();

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

    /**
     * @return the identifier
     */
    public String getIdentifier() {

        return identifier;
    }

    /**
     * @param identifier
     *            the identifier to set
     */
    public void setIdentifier(String identifier) {

        this.identifier = identifier;
    }

    /**
     * @return the fields
     */
    public List<ObjectVariable> getFields() {

        return fields;
    }

    /**
     * @param fields
     *            the fields to set
     */
    public void addField(ObjectVariable variable) {

        fields.add(variable);
    }
}
