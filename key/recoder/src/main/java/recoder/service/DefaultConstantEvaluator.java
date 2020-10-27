package recoder.service;

import recoder.AbstractService;
import recoder.ModelException;
import recoder.ServiceConfiguration;
import recoder.abstraction.Field;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.java.Expression;
import recoder.java.JavaProgramFactory;
import recoder.java.Reference;
import recoder.java.expression.Operator;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.TypeCast;
import recoder.java.reference.*;

import java.util.Stack;

public class DefaultConstantEvaluator extends AbstractService implements ConstantEvaluator {
    static final BinaryNumericOperation PLUS = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a + b;
        }

        public long eval(long a, long b) {
            return a + b;
        }

        public float eval(float a, float b) {
            return a + b;
        }

        public double eval(double a, double b) {
            return a + b;
        }

        public String eval(String a, String b) {
            if (a == null) {
                fail();
                return null;
            }
            return a + b;
        }
    };
    static final BinaryNumericOperation MINUS = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a - b;
        }

        public long eval(long a, long b) {
            return a - b;
        }

        public float eval(float a, float b) {
            return a - b;
        }

        public double eval(double a, double b) {
            return a - b;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    static final BinaryNumericOperation DIVIDE = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a / b;
        }

        public long eval(long a, long b) {
            return a / b;
        }

        public float eval(float a, float b) {
            return a / b;
        }

        public double eval(double a, double b) {
            return a / b;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    static final BinaryNumericOperation MODULO = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a % b;
        }

        public long eval(long a, long b) {
            return a % b;
        }

        public float eval(float a, float b) {
            return a % b;
        }

        public double eval(double a, double b) {
            return a % b;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    static final BinaryNumericOperation TIMES = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a * b;
        }

        public long eval(long a, long b) {
            return a * b;
        }

        public float eval(float a, float b) {
            return a * b;
        }

        public double eval(double a, double b) {
            return a * b;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    static final BinaryNumericOperation SHIFT_LEFT = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a << b;
        }

        public long eval(long a, long b) {
            return a << (int) b;
        }

        public float eval(float a, float b) {
            fail();
            return 0.0F;
        }

        public double eval(double a, double b) {
            fail();
            return 0.0D;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    static final BinaryNumericOperation SHIFT_RIGHT = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a >> b;
        }

        public long eval(long a, long b) {
            return a >> (int) b;
        }

        public float eval(float a, float b) {
            fail();
            return 0.0F;
        }

        public double eval(double a, double b) {
            fail();
            return 0.0D;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    static final BinaryNumericOperation UNSIGNED_SHIFT_RIGHT = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public int eval(int a, int b) {
            return a >>> b;
        }

        public long eval(long a, long b) {
            return a >>> (int) b;
        }

        public float eval(float a, float b) {
            fail();
            return 0.0F;
        }

        public double eval(double a, double b) {
            fail();
            return 0.0D;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    static final BinaryNumericOperation BINARY_AND = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            return a & b;
        }

        public int eval(int a, int b) {
            return a & b;
        }

        public long eval(long a, long b) {
            return a & b;
        }

        public float eval(float a, float b) {
            fail();
            return 0.0F;
        }

        public double eval(double a, double b) {
            fail();
            return 0.0D;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    static final BinaryNumericOperation BINARY_OR = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            return a | b;
        }

        public int eval(int a, int b) {
            return a | b;
        }

        public long eval(long a, long b) {
            return a | b;
        }

        public float eval(float a, float b) {
            fail();
            return 0.0F;
        }

        public double eval(double a, double b) {
            fail();
            return 0.0D;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    static final BinaryNumericOperation BINARY_XOR = new BinaryNumericOperation() {
        public boolean eval(boolean a, boolean b) {
            return a ^ b;
        }

        public int eval(int a, int b) {
            return a ^ b;
        }

        public long eval(long a, long b) {
            return a ^ b;
        }

        public float eval(float a, float b) {
            fail();
            return 0.0F;
        }

        public double eval(double a, double b) {
            fail();
            return 0.0D;
        }

        public String eval(String a, String b) {
            fail();
            return null;
        }
    };
    static final BinaryBooleanOperation EQUALS = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            return (a == b);
        }

        public boolean eval(int a, int b) {
            return (a == b);
        }

        public boolean eval(long a, long b) {
            return (a == b);
        }

        public boolean eval(float a, float b) {
            return (a == b);
        }

        public boolean eval(double a, double b) {
            return (a == b);
        }

        public boolean eval(String a, String b) {
            return (a == b);
        }
    };
    static final BinaryBooleanOperation NOT_EQUALS = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            return (a != b);
        }

        public boolean eval(int a, int b) {
            return (a != b);
        }

        public boolean eval(long a, long b) {
            return (a != b);
        }

        public boolean eval(float a, float b) {
            return (a != b);
        }

        public boolean eval(double a, double b) {
            return (a != b);
        }

        public boolean eval(String a, String b) {
            return (a != b);
        }
    };
    static final BinaryBooleanOperation LESS_THAN = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public boolean eval(int a, int b) {
            return (a < b);
        }

        public boolean eval(long a, long b) {
            return (a < b);
        }

        public boolean eval(float a, float b) {
            return (a < b);
        }

        public boolean eval(double a, double b) {
            return (a < b);
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    static final BinaryBooleanOperation GREATER_THAN = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public boolean eval(int a, int b) {
            return (a > b);
        }

        public boolean eval(long a, long b) {
            return (a > b);
        }

        public boolean eval(float a, float b) {
            return (a > b);
        }

        public boolean eval(double a, double b) {
            return (a > b);
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    static final BinaryBooleanOperation LESS_OR_EQUALS = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public boolean eval(int a, int b) {
            return (a <= b);
        }

        public boolean eval(long a, long b) {
            return (a <= b);
        }

        public boolean eval(float a, float b) {
            return (a <= b);
        }

        public boolean eval(double a, double b) {
            return (a <= b);
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    static final BinaryBooleanOperation GREATER_OR_EQUALS = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            fail();
            return false;
        }

        public boolean eval(int a, int b) {
            return (a >= b);
        }

        public boolean eval(long a, long b) {
            return (a >= b);
        }

        public boolean eval(float a, float b) {
            return (a >= b);
        }

        public boolean eval(double a, double b) {
            return (a >= b);
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    static final BinaryBooleanOperation LOGICAL_AND = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            return (a && b);
        }

        public boolean eval(int a, int b) {
            fail();
            return false;
        }

        public boolean eval(long a, long b) {
            fail();
            return false;
        }

        public boolean eval(float a, float b) {
            fail();
            return false;
        }

        public boolean eval(double a, double b) {
            fail();
            return false;
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    static final BinaryBooleanOperation LOGICAL_OR = new BinaryBooleanOperation() {
        public boolean eval(boolean a, boolean b) {
            return (a || b);
        }

        public boolean eval(int a, int b) {
            fail();
            return false;
        }

        public boolean eval(long a, long b) {
            fail();
            return false;
        }

        public boolean eval(float a, float b) {
            fail();
            return false;
        }

        public boolean eval(double a, double b) {
            fail();
            return false;
        }

        public boolean eval(String a, String b) {
            fail();
            return false;
        }
    };
    static final UnaryBooleanOperation LOGICAL_NOT = new UnaryBooleanOperation() {
        public boolean eval(boolean a) {
            return !a;
        }

        public boolean eval(int a) {
            fail();
            return false;
        }

        public boolean eval(long a) {
            fail();
            return false;
        }

        public boolean eval(float a) {
            fail();
            return false;
        }

        public boolean eval(double a) {
            fail();
            return false;
        }

        public boolean eval(String a) {
            fail();
            return false;
        }
    };
    static final UnaryNumericOperation POSITIVE = new UnaryNumericOperation() {
        public boolean eval(boolean a) {
            fail();
            return false;
        }

        public int eval(int a) {
            return a;
        }

        public long eval(long a) {
            return a;
        }

        public float eval(float a) {
            return a;
        }

        public double eval(double a) {
            return a;
        }

        public String eval(String a) {
            fail();
            return null;
        }
    };
    static final UnaryNumericOperation NEGATIVE = new UnaryNumericOperation() {
        public boolean eval(boolean a) {
            fail();
            return false;
        }

        public int eval(int a) {
            return -a;
        }

        public long eval(long a) {
            return -a;
        }

        public float eval(float a) {
            return -a;
        }

        public double eval(double a) {
            return -a;
        }

        public String eval(String a) {
            fail();
            return null;
        }
    };
    static final UnaryNumericOperation BINARY_NOT = new UnaryNumericOperation() {
        public boolean eval(boolean a) {
            fail();
            return false;
        }

        public int eval(int a) {
            return a ^ 0xFFFFFFFF;
        }

        public long eval(long a) {
            return a ^ 0xFFFFFFFFFFFFFFFFL;
        }

        public float eval(float a) {
            fail();
            return 0.0F;
        }

        public double eval(double a) {
            fail();
            return 0.0D;
        }

        public String eval(String a) {
            fail();
            return null;
        }
    };
    private final Stack visitedVariableReferences;

    public DefaultConstantEvaluator(ServiceConfiguration config) {
        super(config);
        this.visitedVariableReferences = new Stack();
    }

    static int translateType(PrimitiveType t, NameInfo ni) {
        if (t == ni.getIntType())
            return 4;
        if (t == ni.getBooleanType())
            return 0;
        if (t == ni.getLongType())
            return 5;
        if (t == ni.getFloatType())
            return 6;
        if (t == ni.getDoubleType())
            return 7;
        if (t == ni.getByteType())
            return 1;
        if (t == ni.getCharType())
            return 3;
        if (t == ni.getShortType())
            return 2;
        return -1;
    }

    static PrimitiveType translateType(int t, NameInfo ni) {
        switch (t) {
            case 4:
                return ni.getIntType();
            case 0:
                return ni.getBooleanType();
            case 5:
                return ni.getLongType();
            case 6:
                return ni.getFloatType();
            case 7:
                return ni.getDoubleType();
            case 1:
                return ni.getByteType();
            case 3:
                return ni.getCharType();
            case 2:
                return ni.getShortType();
        }
        return null;
    }

    static void promoteNumericTypeToInt(ConstantEvaluator.EvaluationResult res) {
        switch (res.getTypeCode()) {
            case 1:
                res.setInt(res.getByte());
                break;
            case 3:
                res.setInt(res.getChar());
                break;
            case 2:
                res.setInt(res.getShort());
                break;
        }
    }

    static void matchTypes(ConstantEvaluator.EvaluationResult lhs, ConstantEvaluator.EvaluationResult rhs) {
        switch (lhs.getTypeCode()) {
            case 4:
                switch (rhs.getTypeCode()) {
                    case 5:
                        lhs.setLong(lhs.getInt());
                        break;
                    case 6:
                        lhs.setFloat(lhs.getInt());
                        break;
                    case 7:
                        lhs.setDouble(lhs.getInt());
                        break;
                }
                break;
            case 5:
                switch (rhs.getTypeCode()) {
                    case 4:
                        rhs.setLong(rhs.getInt());
                        break;
                    case 6:
                        lhs.setFloat((float) lhs.getLong());
                        break;
                    case 7:
                        lhs.setDouble(lhs.getLong());
                        break;
                }
                break;
            case 6:
                switch (rhs.getTypeCode()) {
                    case 4:
                        rhs.setFloat(rhs.getInt());
                        break;
                    case 5:
                        rhs.setFloat((float) rhs.getLong());
                        break;
                    case 7:
                        lhs.setDouble(lhs.getFloat());
                        break;
                }
                break;
            case 7:
                switch (rhs.getTypeCode()) {
                    case 4:
                        rhs.setDouble(rhs.getInt());
                        break;
                    case 5:
                        rhs.setDouble(rhs.getLong());
                        break;
                    case 6:
                        rhs.setDouble(rhs.getFloat());
                        break;
                }
                break;
            case 8:
                switch (rhs.getTypeCode()) {
                    case 4:
                        rhs.setString(String.valueOf(rhs.getInt()));
                        break;
                    case 5:
                        rhs.setString(String.valueOf(rhs.getLong()));
                        break;
                    case 6:
                        rhs.setString(String.valueOf(rhs.getFloat()));
                        break;
                    case 7:
                        rhs.setString(String.valueOf(rhs.getDouble()));
                        break;
                }
                break;
        }
        if (lhs.getTypeCode() != rhs.getTypeCode())
            throw new RuntimeException("Operand types are illegal: " + lhs.getTypeCode() + " / " + rhs.getTypeCode());
    }

    static void matchAssignmentTypes(ConstantEvaluator.EvaluationResult lhs, ConstantEvaluator.EvaluationResult rhs) {
        int value;
        switch (lhs.getTypeCode()) {
            case 4:
                switch (rhs.getTypeCode()) {
                    case 1:
                        value = lhs.getInt();
                        if (-128 <= value && value <= 127) {
                            lhs.setByte((byte) value);
                        } else {
                            rhs.setInt(rhs.getByte());
                        }
                        return;
                    case 3:
                        value = lhs.getInt();
                        if (0 <= value && value <= 65535) {
                            lhs.setChar((char) value);
                        } else {
                            rhs.setInt(rhs.getChar());
                        }
                        return;
                    case 2:
                        value = lhs.getInt();
                        if (-32768 <= value && value <= 32767) {
                            lhs.setShort((short) value);
                        } else {
                            rhs.setInt(rhs.getShort());
                        }
                        return;
                }
                break;
            case 1:
                if (rhs.getTypeCode() == 4) {
                    value = rhs.getInt();
                    if (-128 <= value && value <= 127) {
                        rhs.setByte((byte) value);
                    } else {
                        lhs.setInt(lhs.getByte());
                    }
                    return;
                }
                break;
            case 2:
                if (rhs.getTypeCode() == 4) {
                    value = rhs.getInt();
                    if (-32768 <= value && value <= 32767) {
                        rhs.setShort((short) value);
                    } else {
                        lhs.setInt(lhs.getShort());
                    }
                    return;
                }
                break;
            case 3:
                if (rhs.getTypeCode() == 4) {
                    value = rhs.getInt();
                    if (0 <= value && value <= 65535) {
                        rhs.setChar((char) value);
                    } else {
                        lhs.setInt(lhs.getChar());
                    }
                    return;
                }
                break;
        }
        matchTypes(lhs, rhs);
    }

    static void matchConditionalTypes(ConstantEvaluator.EvaluationResult lhs, ConstantEvaluator.EvaluationResult rhs) {
        switch (lhs.getTypeCode()) {
            case 1:
                switch (rhs.getTypeCode()) {
                    case 2:
                        lhs.setShort(lhs.getByte());
                        return;
                    case 3:
                        promoteNumericTypeToInt(lhs);
                        promoteNumericTypeToInt(rhs);
                        return;
                }
                break;
            case 3:
                switch (rhs.getTypeCode()) {
                    case 1:
                    case 2:
                        promoteNumericTypeToInt(lhs);
                        promoteNumericTypeToInt(rhs);
                        return;
                }
                break;
            case 2:
                switch (rhs.getTypeCode()) {
                    case 1:
                        rhs.setShort(rhs.getByte());
                        return;
                    case 3:
                        promoteNumericTypeToInt(lhs);
                        promoteNumericTypeToInt(rhs);
                        return;
                }
                break;
        }
        matchAssignmentTypes(lhs, rhs);
    }

    static String parseJavaString(String text) {
        int len = text.length();
        StringBuffer buf = new StringBuffer(len);
        for (int i = 1; i < len - 1; i++) {
            char c = text.charAt(i);
            if (c != '\\') {
                buf.append(c);
            } else {
                int j;
                i++;
                switch (text.charAt(i)) {
                    case 'b':
                        buf.append('\b');
                        break;
                    case 't':
                        buf.append('\t');
                        break;
                    case 'n':
                        buf.append('\n');
                        break;
                    case 'f':
                        buf.append('\f');
                        break;
                    case 'r':
                        buf.append('\r');
                        break;
                    case '"':
                        buf.append('"');
                        break;
                    case '\'':
                        buf.append('\'');
                        break;
                    case '\\':
                        buf.append('\\');
                        break;
                    case 'u':
                        i++;
                        while (text.charAt(i) == 'u')
                            i++;
                        buf.append((char) Integer.parseInt(text.substring(i, i + 4), 16));
                        i += 4;
                        break;
                    case '0':
                    case '1':
                    case '2':
                    case '3':
                    case '4':
                    case '5':
                    case '6':
                    case '7':
                        j = i + 1;
                        while (j < len && text.charAt(j) >= '0' && text.charAt(j) <= '7')
                            j++;
                        buf.append((char) Integer.parseInt(text.substring(i, j), 8));
                        i = j;
                        break;
                    default:
                        throw new ModelException("Bad character representation: " + text);
                }
            }
        }
        return buf.toString();
    }

    static void doPrimitiveTypeCast(int newType, ConstantEvaluator.EvaluationResult res) {
        int oldType = res.getTypeCode();
        if (oldType == newType)
            return;
        if (oldType == 0 || newType == 0)
            throw new ModelException("Cast not allowed");
        switch (oldType) {
            case 1:
                switch (newType) {
                    case 2:
                        res.setShort(res.getByte());
                        return;
                    case 3:
                        res.setChar((char) res.getByte());
                        return;
                    case 4:
                        res.setInt(res.getByte());
                        return;
                    case 5:
                        res.setLong(res.getByte());
                        return;
                    case 6:
                        res.setFloat(res.getByte());
                        return;
                    case 7:
                        res.setDouble(res.getByte());
                        return;
                }
                break;
            case 2:
                switch (newType) {
                    case 1:
                        res.setByte((byte) res.getShort());
                        return;
                    case 3:
                        res.setChar((char) res.getShort());
                        return;
                    case 4:
                        res.setInt(res.getShort());
                        return;
                    case 5:
                        res.setLong(res.getShort());
                        return;
                    case 6:
                        res.setFloat(res.getShort());
                        return;
                    case 7:
                        res.setDouble(res.getShort());
                        return;
                }
                break;
            case 3:
                switch (newType) {
                    case 1:
                        res.setByte((byte) res.getChar());
                        return;
                    case 2:
                        res.setShort((short) res.getChar());
                        return;
                    case 4:
                        res.setInt(res.getChar());
                        return;
                    case 5:
                        res.setLong(res.getChar());
                        return;
                    case 6:
                        res.setFloat(res.getChar());
                        return;
                    case 7:
                        res.setDouble(res.getChar());
                        return;
                }
                break;
            case 4:
                switch (newType) {
                    case 1:
                        res.setByte((byte) res.getInt());
                        return;
                    case 2:
                        res.setShort((short) res.getInt());
                        return;
                    case 3:
                        res.setChar((char) res.getInt());
                        return;
                    case 5:
                        res.setLong(res.getInt());
                        return;
                    case 6:
                        res.setFloat(res.getInt());
                        return;
                    case 7:
                        res.setDouble(res.getInt());
                        return;
                }
                break;
            case 5:
                switch (newType) {
                    case 1:
                        res.setByte((byte) (int) res.getLong());
                        return;
                    case 2:
                        res.setShort((short) (int) res.getLong());
                        return;
                    case 3:
                        res.setChar((char) (int) res.getLong());
                        return;
                    case 4:
                        res.setInt((int) res.getLong());
                        return;
                    case 6:
                        res.setFloat((float) res.getLong());
                        return;
                    case 7:
                        res.setDouble(res.getLong());
                        return;
                }
                break;
            case 6:
                switch (newType) {
                    case 1:
                        res.setByte((byte) (int) res.getFloat());
                        return;
                    case 2:
                        res.setShort((short) (int) res.getFloat());
                        return;
                    case 3:
                        res.setChar((char) (int) res.getFloat());
                        return;
                    case 4:
                        res.setInt((int) res.getFloat());
                        return;
                    case 5:
                        res.setLong((long) res.getFloat());
                        return;
                    case 7:
                        res.setDouble(res.getFloat());
                        return;
                }
                break;
            case 7:
                switch (newType) {
                    case 1:
                        res.setByte((byte) (int) res.getDouble());
                        return;
                    case 2:
                        res.setShort((short) (int) res.getDouble());
                        return;
                    case 3:
                        res.setChar((char) (int) res.getDouble());
                        return;
                    case 4:
                        res.setInt((int) res.getDouble());
                        return;
                    case 5:
                        res.setLong((long) res.getDouble());
                        return;
                    case 6:
                        res.setFloat((float) res.getDouble());
                        return;
                }
                break;
        }
    }

    NameInfo getNameInfo() {
        return this.serviceConfiguration.getNameInfo();
    }

    SourceInfo getSourceInfo() {
        return this.serviceConfiguration.getSourceInfo();
    }

    public Type getCompileTimeConstantType(Expression expr) {
        ConstantEvaluator.EvaluationResult res = new ConstantEvaluator.EvaluationResult();
        if (!isCompileTimeConstant(expr, res))
            return null;
        return res.getPrimitiveType(getNameInfo());
    }

    public boolean isCompileTimeConstant(Expression expr) {
        return isCompileTimeConstant(expr, new ConstantEvaluator.EvaluationResult());
    }

    public boolean isCompileTimeConstant(Expression expr, ConstantEvaluator.EvaluationResult res) {
        VariableReference variableReference;
        if (expr instanceof recoder.java.expression.Literal) {
            if (expr instanceof IntLiteral) {
                String v = ((IntLiteral) expr).getValue();
                res.setInt(JavaProgramFactory.parseInt(v));
                return true;
            }
            if (expr instanceof StringLiteral) {
                res.setString(parseJavaString(((StringLiteral) expr).getValue()));
                return true;
            }
            if (expr instanceof BooleanLiteral) {
                res.setBoolean(((BooleanLiteral) expr).getValue());
                return true;
            }
            if (expr instanceof recoder.java.expression.literal.NullLiteral) {
                res.setString(null);
                return true;
            }
            if (expr instanceof CharLiteral) {
                res.setChar(parseJavaString(((CharLiteral) expr).getValue()).charAt(0));
                return true;
            }
            if (expr instanceof LongLiteral) {
                String v = ((LongLiteral) expr).getValue();
                res.setLong(JavaProgramFactory.parseLong(v));
                return true;
            }
            if (expr instanceof FloatLiteral) {
                String v = ((FloatLiteral) expr).getValue();
                res.setFloat(Float.valueOf(v).floatValue());
                return true;
            }
            if (expr instanceof DoubleLiteral) {
                String v = ((DoubleLiteral) expr).getValue();
                res.setDouble(Double.valueOf(v).doubleValue());
                return true;
            }
            throw new ModelException("Unknown literal type");
        }
        if (expr instanceof Operator) {
            boolean cond;
            if (expr instanceof recoder.java.expression.Assignment)
                return false;
            Operator op = (Operator) expr;
            if (op instanceof recoder.java.expression.operator.TypeOperator) {
                if (op instanceof TypeCast) {
                    if (!isCompileTimeConstant(((TypeCast) expr).getExpressionAt(0), res))
                        return false;
                    int newType = -1;
                    Type to = getSourceInfo().getType(((TypeCast) expr).getTypeReference());
                    if (to instanceof PrimitiveType) {
                        newType = translateType((PrimitiveType) to, getNameInfo());
                    } else {
                        if (to == getNameInfo().getJavaLangString()) {
                            newType = 8;
                            return res.getTypeCode() == 8;
                        }
                        return false;
                    }
                    doPrimitiveTypeCast(newType, res);
                    return true;
                }
                return false;
            }
            if (op instanceof recoder.java.expression.ParenthesizedExpression)
                return isCompileTimeConstant(op.getExpressionAt(0), res);
            promoteNumericTypeToInt(res);
            ConstantEvaluator.EvaluationResult lhs = null;
            ConstantEvaluator.EvaluationResult rhs = null;
            UnaryNumericOperation uno = null;
            UnaryBooleanOperation ubo = null;
            BinaryNumericOperation bno = null;
            BinaryBooleanOperation bbo = null;
            switch (op.getArity()) {
                case 1:
                    if (!isCompileTimeConstant(op.getExpressionAt(0), res))
                        return false;
                    if (op instanceof recoder.java.expression.operator.Positive) {
                        uno = POSITIVE;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.Negative) {
                        uno = NEGATIVE;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.BinaryNot) {
                        uno = BINARY_NOT;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.LogicalNot)
                        ubo = LOGICAL_NOT;
                    break;
                case 2:
                    if (!isCompileTimeConstant(op.getExpressionAt(0), res))
                        return false;
                    lhs = res;
                    promoteNumericTypeToInt(lhs);
                    rhs = new ConstantEvaluator.EvaluationResult();
                    if (!isCompileTimeConstant(op.getExpressionAt(1), rhs))
                        return false;
                    promoteNumericTypeToInt(rhs);
                    matchTypes(lhs, rhs);
                    if (op instanceof recoder.java.expression.operator.ComparativeOperator) {
                        if (op instanceof recoder.java.expression.operator.Equals) {
                            bbo = EQUALS;
                            break;
                        }
                        if (op instanceof recoder.java.expression.operator.NotEquals) {
                            bbo = NOT_EQUALS;
                            break;
                        }
                        if (op instanceof recoder.java.expression.operator.GreaterThan) {
                            bbo = GREATER_THAN;
                            break;
                        }
                        if (op instanceof recoder.java.expression.operator.LessThan) {
                            bbo = LESS_THAN;
                            break;
                        }
                        if (op instanceof recoder.java.expression.operator.GreaterOrEquals) {
                            bbo = GREATER_OR_EQUALS;
                            break;
                        }
                        if (op instanceof recoder.java.expression.operator.LessOrEquals) {
                            bbo = LESS_OR_EQUALS;
                            break;
                        }
                        if (op instanceof recoder.java.expression.operator.LogicalAnd) {
                            bbo = LOGICAL_AND;
                            break;
                        }
                        if (op instanceof recoder.java.expression.operator.LogicalOr)
                            bbo = LOGICAL_OR;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.Plus) {
                        bno = PLUS;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.Minus) {
                        bno = MINUS;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.Times) {
                        bno = TIMES;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.Divide) {
                        bno = DIVIDE;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.Modulo) {
                        bno = MODULO;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.ShiftLeft) {
                        bno = SHIFT_LEFT;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.ShiftRight) {
                        bno = SHIFT_RIGHT;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.UnsignedShiftRight) {
                        bno = UNSIGNED_SHIFT_RIGHT;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.BinaryAnd) {
                        bno = BINARY_AND;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.BinaryOr) {
                        bno = BINARY_OR;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.BinaryXOr) {
                        bno = BINARY_XOR;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.LogicalAnd) {
                        bbo = LOGICAL_AND;
                        break;
                    }
                    if (op instanceof recoder.java.expression.operator.LogicalOr)
                        bbo = LOGICAL_OR;
                    break;
                case 3:
                    if (!isCompileTimeConstant(op.getExpressionAt(0), res))
                        return false;
                    if (res.getTypeCode() != 0)
                        throw new ModelException("No boolean expression in ?:");
                    cond = res.getBoolean();
                    lhs = res;
                    if (!isCompileTimeConstant(op.getExpressionAt(1), lhs))
                        return false;
                    rhs = new ConstantEvaluator.EvaluationResult();
                    if (!isCompileTimeConstant(op.getExpressionAt(2), rhs))
                        return false;
                    matchConditionalTypes(lhs, rhs);
                    switch (lhs.getTypeCode()) {
                        case 0:
                            res.setBoolean(cond ? lhs.getBoolean() : rhs.getBoolean());
                            break;
                        case 1:
                            res.setByte(cond ? lhs.getByte() : rhs.getByte());
                            break;
                        case 2:
                            res.setShort(cond ? lhs.getShort() : rhs.getShort());
                            break;
                        case 3:
                            res.setChar(cond ? lhs.getChar() : rhs.getChar());
                            break;
                        case 4:
                            res.setInt(cond ? lhs.getInt() : rhs.getInt());
                            break;
                        case 5:
                            res.setLong(cond ? lhs.getLong() : rhs.getLong());
                            break;
                        case 6:
                            res.setFloat(cond ? lhs.getFloat() : rhs.getFloat());
                            break;
                        case 7:
                            res.setDouble(cond ? lhs.getDouble() : rhs.getDouble());
                            break;
                        case 8:
                            res.setString(cond ? lhs.getString() : rhs.getString());
                            break;
                    }
                    return true;
            }
            if (bno != null) {
                switch (lhs.getTypeCode()) {
                    case 0:
                        lhs.setBoolean(bno.eval(lhs.getBoolean(), rhs.getBoolean()));
                        break;
                    case 4:
                        lhs.setInt(bno.eval(lhs.getInt(), rhs.getInt()));
                        break;
                    case 5:
                        lhs.setLong(bno.eval(lhs.getLong(), rhs.getLong()));
                        break;
                    case 6:
                        lhs.setFloat(bno.eval(lhs.getFloat(), rhs.getFloat()));
                        break;
                    case 7:
                        lhs.setDouble(bno.eval(lhs.getDouble(), rhs.getDouble()));
                        break;
                    case 8:
                        lhs.setString(bno.eval(lhs.getString(), rhs.getString()));
                        break;
                }
                return true;
            }
            if (bbo != null) {
                switch (lhs.getTypeCode()) {
                    case 0:
                        lhs.setBoolean(bbo.eval(lhs.getBoolean(), rhs.getBoolean()));
                        break;
                    case 4:
                        lhs.setBoolean(bbo.eval(lhs.getInt(), rhs.getInt()));
                        break;
                    case 5:
                        lhs.setBoolean(bbo.eval(lhs.getLong(), rhs.getLong()));
                        break;
                    case 6:
                        lhs.setBoolean(bbo.eval(lhs.getFloat(), rhs.getFloat()));
                        break;
                    case 7:
                        lhs.setBoolean(bbo.eval(lhs.getDouble(), rhs.getDouble()));
                        break;
                    case 8:
                        lhs.setBoolean(bbo.eval(lhs.getString(), rhs.getString()));
                        break;
                }
                return true;
            }
            if (uno != null) {
                switch (res.getTypeCode()) {
                    case 0:
                        res.setBoolean(uno.eval(res.getBoolean()));
                        break;
                    case 4:
                        res.setInt(uno.eval(res.getInt()));
                        break;
                    case 5:
                        res.setLong(uno.eval(res.getLong()));
                        break;
                    case 6:
                        res.setFloat(uno.eval(res.getFloat()));
                        break;
                    case 7:
                        res.setDouble(uno.eval(res.getDouble()));
                        break;
                    case 8:
                        res.setString(uno.eval(res.getString()));
                        break;
                }
                return true;
            }
            if (ubo != null) {
                switch (res.getTypeCode()) {
                    case 0:
                        res.setBoolean(ubo.eval(res.getBoolean()));
                        break;
                    case 4:
                        res.setBoolean(ubo.eval(res.getInt()));
                        break;
                    case 5:
                        res.setBoolean(ubo.eval(res.getLong()));
                        break;
                    case 6:
                        res.setBoolean(ubo.eval(res.getFloat()));
                        break;
                    case 7:
                        res.setBoolean(ubo.eval(res.getDouble()));
                        break;
                    case 8:
                        res.setBoolean(ubo.eval(res.getString()));
                        break;
                }
                return true;
            }
            throw new ModelException("Unknown operator " + op.getClass().getName() + "?!");
        }
        if (expr instanceof UncollatedReferenceQualifier) {
            Reference reference = getSourceInfo().resolveURQ((UncollatedReferenceQualifier) expr);
            if (reference instanceof VariableReference) {
                variableReference = (VariableReference) reference;
            } else {
                return false;
            }
        }
        if (variableReference instanceof VariableReference) {
            if (variableReference instanceof FieldReference) {
                ReferencePrefix pre = ((FieldReference) variableReference).getReferencePrefix();
                while (pre != null) {
                    if (pre instanceof FieldReference || pre instanceof recoder.java.reference.PackageReference || pre instanceof recoder.java.reference.TypeReference || pre instanceof UncollatedReferenceQualifier) {
                        pre = ((ReferenceSuffix) pre).getReferencePrefix();
                        continue;
                    }
                    return false;
                }
            }
            Variable v = getSourceInfo().getVariable(variableReference);
            if (v == null || !v.isFinal() || (v instanceof Field && !((Field) v).isStatic()))
                return false;
            int vtype = -1;
            Type vt = v.getType();
            if (vt instanceof PrimitiveType) {
                vtype = translateType((PrimitiveType) vt, getNameInfo());
            } else if (vt == getNameInfo().getJavaLangString()) {
                vtype = 8;
            }
            if (vtype == -1)
                return false;
            if (this.visitedVariableReferences.contains(variableReference))
                return false;
            this.visitedVariableReferences.push(variableReference);
            try {
                ProgramModelInfo qs = v.getProgramModelInfo();
                if (qs instanceof SourceInfo) {
                    SourceInfo ais = (SourceInfo) qs;
                    Expression expression = ais.getVariableSpecification(v).getInitializer();
                    if (expression == null)
                        return false;
                    if (!isCompileTimeConstant(expression, res))
                        return false;
                    doPrimitiveTypeCast(vtype, res);
                    return true;
                }
                if (qs instanceof ByteCodeInfo) {
                    ByteCodeInfo bis = (ByteCodeInfo) qs;
                    String val = bis.getFieldInfo((Field) v).getConstantValue();
                    if (val == null)
                        return false;
                    switch (vtype) {
                        case 0:
                            res.setBoolean((Integer.parseInt(val) != 0));
                            break;
                        case 1:
                            res.setByte((byte) Integer.parseInt(val));
                            break;
                        case 2:
                            res.setShort((short) Integer.parseInt(val));
                            break;
                        case 3:
                            res.setChar((char) Integer.parseInt(val));
                            break;
                        case 4:
                            res.setInt(Integer.parseInt(val));
                            break;
                        case 5:
                            res.setLong(Long.parseLong(val));
                            break;
                        case 6:
                            if (val.equals("NaN")) {
                                res.setFloat(Float.NaN);
                                break;
                            }
                            res.setFloat(Float.valueOf(val).floatValue());
                            break;
                        case 7:
                            if (val.equals("NaN")) {
                                res.setDouble(Double.NaN);
                                break;
                            }
                            res.setDouble(Double.valueOf(val).doubleValue());
                            break;
                        case 8:
                            res.setString(val);
                            break;
                    }
                    return true;
                }
            } finally {
                this.visitedVariableReferences.pop();
            }
            return false;
        }
        return false;
    }

    static abstract class Operation {
        protected void fail() {
            throw new ModelException("Operand types are illegal");
        }
    }

    static abstract class BinaryNumericOperation extends Operation {
        public abstract boolean eval(boolean param1Boolean1, boolean param1Boolean2);

        public abstract int eval(int param1Int1, int param1Int2);

        public abstract long eval(long param1Long1, long param1Long2);

        public abstract float eval(float param1Float1, float param1Float2);

        public abstract double eval(double param1Double1, double param1Double2);

        public abstract String eval(String param1String1, String param1String2);
    }

    static abstract class BinaryBooleanOperation extends Operation {
        public abstract boolean eval(boolean param1Boolean1, boolean param1Boolean2);

        public abstract boolean eval(int param1Int1, int param1Int2);

        public abstract boolean eval(long param1Long1, long param1Long2);

        public abstract boolean eval(float param1Float1, float param1Float2);

        public abstract boolean eval(double param1Double1, double param1Double2);

        public abstract boolean eval(String param1String1, String param1String2);
    }

    static abstract class UnaryNumericOperation extends Operation {
        public abstract boolean eval(boolean param1Boolean);

        public abstract int eval(int param1Int);

        public abstract long eval(long param1Long);

        public abstract float eval(float param1Float);

        public abstract double eval(double param1Double);

        public abstract String eval(String param1String);
    }

    static abstract class UnaryBooleanOperation extends Operation {
        public abstract boolean eval(boolean param1Boolean);

        public abstract boolean eval(int param1Int);

        public abstract boolean eval(long param1Long);

        public abstract boolean eval(float param1Float);

        public abstract boolean eval(double param1Double);

        public abstract boolean eval(String param1String);
    }
}
