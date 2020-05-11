package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.speclang.PositionedString;

/**
 * @author Alexander Weigl
 * @version 1 (5/10/20)
 */
public class JmlFacade {
    static ANTLRStringStream createANTLRStringStream(PositionedString ps) {
        ANTLRStringStream result = new ANTLRStringStream(ps.text);
        result.name = ps.fileName;
        result.setCharPositionInLine(ps.pos.getColumn());
        result.setLine(ps.pos.getLine() + 1);
        return result;
    }

}
