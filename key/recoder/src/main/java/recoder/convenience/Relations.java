package recoder.convenience;

import recoder.ModelElement;
import recoder.java.Identifier;
import recoder.java.NamedProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.expression.literal.*;
import recoder.util.HashCode;
import recoder.util.Order;

public class Relations {
    public static final HashCode STRUCTURAL_EQUALITY = new HashCode() {
        public int hashCode(Object x) {
            if (x instanceof recoder.java.ProgramElement) {
                int res = getClass().hashCode();
                if (x instanceof NonTerminalProgramElement) {
                    if (x instanceof NamedProgramElement) {
                        String name = ((NamedProgramElement) x).getName();
                        if (name != null)
                            res ^= name.hashCode();
                    }
                    res += ((NonTerminalProgramElement) x).getChildCount();
                }
                return res;
            }
            if (x == null)
                return 0;
            throw new IllegalArgumentException("Structural hashcodes are only defined for program elements");
        }

        public boolean equals(Object x, Object y) {
            if (x == null || y == null)
                return false;
            if (x instanceof NonTerminalProgramElement) {
                if (x.getClass() != y.getClass())
                    if (x instanceof recoder.java.reference.UncollatedReferenceQualifier) {
                        if (!(y instanceof recoder.java.reference.ArrayLengthReference) && !(y instanceof recoder.java.reference.FieldReference) && !(y instanceof recoder.java.reference.PackageReference) && !(y instanceof recoder.java.reference.TypeReference) && !(y instanceof recoder.java.reference.VariableReference))
                            return false;
                    } else if (y instanceof recoder.java.reference.UncollatedReferenceQualifier) {
                        if (!(x instanceof recoder.java.reference.ArrayLengthReference) && !(x instanceof recoder.java.reference.FieldReference) && !(x instanceof recoder.java.reference.PackageReference) && !(x instanceof recoder.java.reference.TypeReference) && !(x instanceof recoder.java.reference.VariableReference))
                            return false;
                    } else {
                        return false;
                    }
                NonTerminalProgramElement a = (NonTerminalProgramElement) x;
                NonTerminalProgramElement b = (NonTerminalProgramElement) y;
                int n = a.getChildCount();
                int m = b.getChildCount();
                if (a instanceof recoder.java.reference.ArrayLengthReference && b instanceof recoder.java.reference.UncollatedReferenceQualifier)
                    m--;
                if (b instanceof recoder.java.reference.ArrayLengthReference && a instanceof recoder.java.reference.UncollatedReferenceQualifier)
                    n--;
                if (n != m)
                    return false;
                for (int i = 0; i < n; i++) {
                    if (!equals(a.getChildAt(i), b.getChildAt(i)))
                        return false;
                }
                return true;
            }
            if (x instanceof recoder.java.TerminalProgramElement) {
                if (x.getClass() != y.getClass())
                    return false;
                if (x instanceof Identifier)
                    return ((Identifier) x).getText().equals(((Identifier) y).getText());
                if (x instanceof recoder.java.expression.Literal) {
                    if (x instanceof IntLiteral)
                        return ((IntLiteral) x).getValue().equals(((IntLiteral) y).getValue());
                    if (x instanceof BooleanLiteral)
                        return (((BooleanLiteral) x).getValue() == ((BooleanLiteral) y).getValue());
                    if (x instanceof StringLiteral)
                        return ((StringLiteral) x).getValue().equals(((StringLiteral) y).getValue());
                    if (x instanceof recoder.java.expression.literal.NullLiteral)
                        return true;
                    if (x instanceof CharLiteral)
                        return ((CharLiteral) x).getValue().equals(((CharLiteral) y).getValue());
                    if (x instanceof DoubleLiteral)
                        return ((DoubleLiteral) x).getValue().equals(((DoubleLiteral) y).getValue());
                    if (x instanceof LongLiteral)
                        return ((LongLiteral) x).getValue().equals(((LongLiteral) y).getValue());
                    if (x instanceof FloatLiteral)
                        return ((FloatLiteral) x).getValue().equals(((FloatLiteral) y).getValue());
                }
                return true;
            }
            throw new IllegalArgumentException("Structural equality is only defined for program elements");
        }
    };
    public static final Order NAMED_MODEL_ELEMENT_ORDER = new ModelElementLexicalOrder("%n");
    public static final Order UNAMBIGUOUS_ORDER = new ModelElementLexicalOrder("%u|%p|%N");

    public static class ModelElementLexicalOrder extends Order.CustomLexicalOrder {
        private final String format;

        public ModelElementLexicalOrder(String format) {
            if (format == null)
                throw new IllegalArgumentException("Format must not be nulL");
            this.format = format;
        }

        public boolean isComparable(Object x, Object y) {
            return ((x == null && y == null) || (x instanceof ModelElement && y instanceof ModelElement));
        }

        protected String toString(Object x) {
            return Format.toString(this.format, (ModelElement) x);
        }
    }
}
