package de.uka.ilkd.key.testgeneration.xmlparser.junitparser;

/**
 * Instances of this bean represent variable declarations in a Java source file.
 * 
 * @author christopher
 */
public class ObjectVariable {

    /**
     * Identifier for this variable.
     */
    private String identifier;

    /**
     * Type of this variable.
     */
    private String type;
    
    private String reference;

    /**
     * Flags whether this variable is declared final or not.
     */
    private boolean isfinal;

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
     * @return the isfinal
     */
    public boolean isIsfinal() {

        return isfinal;
    }

    /**
     * @param isfinal
     *            the isfinal to set
     */
    public void setIsfinal(boolean isfinal) {

        this.isfinal = isfinal;
    }

    
    /**
     * @return the reference
     */
    public String getReference() {
    
        return reference;
    }

    
    /**
     * @param reference the reference to set
     */
    public void setReference(String reference) {
    
        this.reference = reference;
    }
}
