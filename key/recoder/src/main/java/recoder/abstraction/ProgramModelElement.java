package recoder.abstraction;

import recoder.ModelElement;
import recoder.NamedModelElement;
import recoder.bytecode.AccessFlags;
import recoder.convenience.Format;
import recoder.service.ProgramModelInfo;
import recoder.util.Order;

public interface ProgramModelElement extends NamedModelElement, AccessFlags {
    Order LEXICAL_ORDER = new LexicalOrder();

    String getFullName();

    ProgramModelInfo getProgramModelInfo();

    void setProgramModelInfo(ProgramModelInfo paramProgramModelInfo);

    class LexicalOrder implements Order {
        public final int hashCode(Object x) {
            if (x == null)
                return 0;
            String name = Format.toString("%N|%p|%u", (ModelElement) x);
            if (name == null)
                return 0;
            return name.hashCode();
        }

        public final boolean isComparable(Object x, Object y) {
            return true;
        }

        private int diff(ProgramModelElement n1, ProgramModelElement n2) {
            if (n1 == n2)
                return 0;
            String s1 = (n1 == null) ? "" : Format.toString("%N", n1);
            String s2 = (n2 == null) ? "" : Format.toString("%N", n2);
            int res = diff(s1, s2);
            if (res == 0) {
                s1 = Format.toString("%p|%u", n1);
                s2 = Format.toString("%p|%u", n2);
                res = diff(s1, s2);
            }
            return res;
        }

        private int diff(String s1, String s2) {
            if (s1 == null)
                s1 = "";
            if (s2 == null)
                s2 = "";
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
            return (diff((ProgramModelElement) x, (ProgramModelElement) y) == 0);
        }

        public final boolean less(Object x, Object y) {
            return (diff((ProgramModelElement) x, (ProgramModelElement) y) < 0);
        }

        public final boolean greater(Object x, Object y) {
            return (diff((ProgramModelElement) x, (ProgramModelElement) y) > 0);
        }

        public final boolean lessOrEquals(Object x, Object y) {
            return (diff((ProgramModelElement) x, (ProgramModelElement) y) <= 0);
        }

        public final boolean greaterOrEquals(Object x, Object y) {
            return (diff((ProgramModelElement) x, (ProgramModelElement) y) >= 0);
        }
    }
}
