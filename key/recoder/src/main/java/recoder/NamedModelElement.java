package recoder;

import recoder.util.Order;

public interface NamedModelElement extends ModelElement {
    Order LEXICAL_ORDER = new LexicalOrder();

    String getName();

    class LexicalOrder extends Order.CustomLexicalOrder {
        protected String toString(Object x) {
            return (x == null) ? "" : ((NamedModelElement) x).getName();
        }

        public boolean isComparable(Object x, Object y) {
            return ((x == null && y == null) || (x instanceof NamedModelElement && y instanceof NamedModelElement));
        }
    }
}
