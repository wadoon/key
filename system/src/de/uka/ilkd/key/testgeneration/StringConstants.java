package de.uka.ilkd.key.testgeneration;

/**
 * Contains symbolic labels which need to be used in a uniform manner in all
 * subsystems of KeYTestGen.
 * 
 * @author christopher
 * 
 */
public enum StringConstants {

    SELF("self"),
    NEWLINE("\n"),
    TAB("    "),
    FIELD_SEPARATOR("_");
    ;
    

    private StringConstants(String keyWord) {
        this.keyWord = keyWord;
    }

    private final String keyWord;

    @Override
    public String toString() {
        return keyWord;
    }
}
