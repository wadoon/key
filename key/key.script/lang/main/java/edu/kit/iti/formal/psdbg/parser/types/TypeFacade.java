package edu.kit.iti.formal.psdbg.parser.types;

import java.util.Arrays;

/**
 * @author Alexander Weigl
 * @version 1 (15.08.17)
 */
public final class TypeFacade {
    public static final Type ANY_TERM = new TermType();

    public static TermType getTermType(String symbol) {
        if ("TERM".equalsIgnoreCase(symbol)) {
            return new TermType();
        }
        if (symbol.toLowerCase().startsWith("term<") && symbol.endsWith(">")) {
            TermType tt = new TermType();
            //get the termtype
            String n = symbol.substring(5, symbol.length() - 1);
            for (String term : n.split(",")) {
                tt.getArgTypes().add(findType(term));
            }
            return tt;
        }

        return null;
    }

    public static Type findType(String n) {
        TermType tt = getTermType(n);
        if (tt != null) return tt;
        return getSimpleType(n);
    }

    public static SimpleType getSimpleType(String n) {
        for (SimpleType t : SimpleType.values()) {
            if (t.symbol().equalsIgnoreCase(n))
                return t;
        }
        throw new IllegalStateException("SimpleType " + n + " is not defined. Valid types are: " + Arrays.toString(SimpleType.values()));
    }

    public static boolean isTerm(Type type) {
        return type instanceof TermType;
    }
}
