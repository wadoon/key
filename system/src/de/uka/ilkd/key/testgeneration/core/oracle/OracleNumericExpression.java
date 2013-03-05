package de.uka.ilkd.key.testgeneration.core.oracle;

public abstract class OracleNumericExpression {

    public enum NumericType {
        INTEGER("int"), FLOAT("float"), BYTE("byte"), LONG("long"), DOUBLE(
                "double");

        private final String identifier;

        private NumericType(String identifier) {
            this.identifier = identifier;
        }

        public String toString() {
            return identifier;
        }
    }
    
    private final NumericType type;
    
    public OracleNumericExpression(NumericType type) {
        this.type = type;
    }
    
    private final NumericType getType() {
        return type;
    }
}