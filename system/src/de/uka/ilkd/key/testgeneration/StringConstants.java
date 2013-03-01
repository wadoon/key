package de.uka.ilkd.key.testgeneration;

/**
 * Contains symbolic labels which need to be used in a uniform manner in all
 * subsystems of KeYTestGen.
 * 
 * @author christopher
 * 
 */
public enum StringConstants {

    SELF("self"), NEWLINE("\n"), TAB("    "), FIELD_SEPARATOR("_");
    ;

    private final String keyWord;

    private StringConstants(final String keyWord) {
        this.keyWord = keyWord;
    }

    @Override
    public String toString() {
        return keyWord;
    }
}
