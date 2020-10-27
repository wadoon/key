package recoder.util;

public interface Order extends Equality {
    Order NATURAL = new Natural();
    Order IDENTITY = new Identity();
    Order LEXICAL = new Lexical();

    boolean isComparable(Object paramObject1, Object paramObject2);

    boolean less(Object paramObject1, Object paramObject2);

    boolean greater(Object paramObject1, Object paramObject2);

    boolean lessOrEquals(Object paramObject1, Object paramObject2);

    boolean greaterOrEquals(Object paramObject1, Object paramObject2);

    class Natural implements Order, HashCode {
        public final boolean equals(Object x, Object y) {
            return x.equals(y);
        }

        public final int hashCode(Object x) {
            return x.hashCode();
        }

        public final boolean isComparable(Object x, Object y) {
            return (x != null && y != null);
        }

        public final boolean less(Object x, Object y) {
            return (x.hashCode() < y.hashCode());
        }

        public final boolean greater(Object x, Object y) {
            return (x.hashCode() > y.hashCode());
        }

        public final boolean lessOrEquals(Object x, Object y) {
            return (x.hashCode() <= y.hashCode());
        }

        public final boolean greaterOrEquals(Object x, Object y) {
            return (x.hashCode() >= y.hashCode());
        }
    }

    class Identity implements Order, HashCode {
        public final boolean equals(Object x, Object y) {
            return (x == y);
        }

        public final int hashCode(Object x) {
            return System.identityHashCode(x);
        }

        public final boolean isComparable(Object x, Object y) {
            return true;
        }

        public final boolean less(Object x, Object y) {
            return (System.identityHashCode(x) < System.identityHashCode(x));
        }

        public final boolean greater(Object x, Object y) {
            return (System.identityHashCode(x) > System.identityHashCode(x));
        }

        public final boolean lessOrEquals(Object x, Object y) {
            return (System.identityHashCode(x) <= System.identityHashCode(x));
        }

        public final boolean greaterOrEquals(Object x, Object y) {
            return (System.identityHashCode(x) >= System.identityHashCode(x));
        }
    }

    abstract class CustomLexicalOrder implements Order, HashCode {
        protected abstract String toString(Object param1Object);

        public final int hashCode(Object x) {
            return toString(x).hashCode();
        }

        public boolean isComparable(Object x, Object y) {
            return true;
        }

        private int diff(Object x, Object y) {
            String s1 = toString(x);
            String s2 = toString(y);
            int len1 = s1.length();
            int len2 = s2.length();
            for (int i = 0, m = Math.min(len1, len2); i < m; i++) {
                char c1 = s1.charAt(i);
                char c2 = s2.charAt(i);
                if (c1 != c2)
                    return c1 - c2;
            }
            return len1 - len2;
        }

        public final boolean equals(Object x, Object y) {
            return (diff(x, y) == 0);
        }

        public final boolean less(Object x, Object y) {
            return (diff(x, y) < 0);
        }

        public final boolean greater(Object x, Object y) {
            return (diff(x, y) > 0);
        }

        public final boolean lessOrEquals(Object x, Object y) {
            return (diff(x, y) <= 0);
        }

        public final boolean greaterOrEquals(Object x, Object y) {
            return (diff(x, y) >= 0);
        }
    }

    class Lexical extends CustomLexicalOrder {
        protected String toString(Object x) {
            return x.toString();
        }

        public final boolean isComparable(Object x, Object y) {
            return (x != null && y != null);
        }
    }
}
