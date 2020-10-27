package recoder.service;

import recoder.Service;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.java.Expression;

public interface ConstantEvaluator extends Service {
    int BOOLEAN_TYPE = 0;

    int BYTE_TYPE = 1;

    int SHORT_TYPE = 2;

    int CHAR_TYPE = 3;

    int INT_TYPE = 4;

    int LONG_TYPE = 5;

    int FLOAT_TYPE = 6;

    int DOUBLE_TYPE = 7;

    int STRING_TYPE = 8;

    Type getCompileTimeConstantType(Expression paramExpression);

    boolean isCompileTimeConstant(Expression paramExpression);

    boolean isCompileTimeConstant(Expression paramExpression, EvaluationResult paramEvaluationResult);

    final class EvaluationResult {
        private int type = -1;

        private boolean booleanValue;

        private byte byteValue;

        private short shortValue;

        private char charValue;

        private int intValue;

        private long longValue;

        private float floatValue;

        private double doubleValue;

        private String stringValue;

        public PrimitiveType getPrimitiveType(NameInfo ni) {
            return DefaultConstantEvaluator.translateType(this.type, ni);
        }

        public int getTypeCode() {
            return this.type;
        }

        public boolean getBoolean() {
            return this.booleanValue;
        }

        public void setBoolean(boolean value) {
            this.booleanValue = value;
            this.type = 0;
        }

        public byte getByte() {
            return this.byteValue;
        }

        public void setByte(byte value) {
            this.byteValue = value;
            this.type = 1;
        }

        public short getShort() {
            return this.shortValue;
        }

        public void setShort(short value) {
            this.shortValue = value;
            this.type = 2;
        }

        public char getChar() {
            return this.charValue;
        }

        public void setChar(char value) {
            this.charValue = value;
            this.type = 3;
        }

        public int getInt() {
            return this.intValue;
        }

        public void setInt(int value) {
            this.intValue = value;
            this.type = 4;
        }

        public long getLong() {
            return this.longValue;
        }

        public void setLong(long value) {
            this.longValue = value;
            this.type = 5;
        }

        public float getFloat() {
            return this.floatValue;
        }

        public void setFloat(float value) {
            this.floatValue = value;
            this.type = 6;
        }

        public double getDouble() {
            return this.doubleValue;
        }

        public void setDouble(double value) {
            this.doubleValue = value;
            this.type = 7;
        }

        public String getString() {
            return this.stringValue;
        }

        public void setString(String value) {
            this.stringValue = (value == null) ? null : value.intern();
            this.type = 8;
        }

        public String toString() {
            switch (this.type) {
                case 0:
                    return String.valueOf(this.booleanValue);
                case 1:
                    return String.valueOf(this.byteValue);
                case 2:
                    return String.valueOf(this.shortValue);
                case 3:
                    return String.valueOf(this.charValue);
                case 4:
                    return String.valueOf(this.intValue);
                case 5:
                    return String.valueOf(this.longValue);
                case 6:
                    return String.valueOf(this.floatValue);
                case 7:
                    return String.valueOf(this.doubleValue);
                case 8:
                    return "\"" + this.stringValue + "\"";
            }
            return "Unknown type";
        }
    }
}
