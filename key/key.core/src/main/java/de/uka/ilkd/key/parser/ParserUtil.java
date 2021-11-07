package de.uka.ilkd.key.parser;

import com.github.javaparser.Token;
import com.github.javaparser.ast.expr.*;
import de.uka.ilkd.key.util.parsing.LocatableException;

import java.net.URL;

/**
 * @author Alexander Weigl
 * @version 1 (6/21/21)
 */
public final class ParserUtil {
    /**
     * Throws an exception if the given expression is invalid in a {@code \singleton} constructor.
     * The given token is used for positional information.
     */
    public static void checkValidSingletonReference(Expression expr, Token tok) {
        //weigl: I hope I catch them all.
        if (expr instanceof NameExpr
                || expr instanceof ThisExpr
                || expr instanceof SuperExpr
                || expr instanceof FieldAccessExpr) {
            return;
        }
        Location loc = new Location((URL) null, tok.beginLine, tok.beginColumn);
        throw new LocatableException("Given non-reference as parameter for \\singleton", loc);
    }
}
