package de.uka.ilkd.key.testgeneration;

/**
 * Contains symbolic labels which need to be used in a uniform manner in all
 * subsystems of KeYTestGen.
 * 
 * @author christopher
 * 
 */
public enum StringConstants {

    FIELD_SEPARATOR("_"), NEWLINE("\n"), SELF("self"), TAB("    ");
    ;

    private final String keyWord;

    private StringConstants(final String keyWord) {
        this.keyWord = keyWord;
    }

    @Override
    public String toString() {
        return this.keyWord;
    }
}
