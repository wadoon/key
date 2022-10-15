package antlr;

import org.fife.ui.rsyntaxtextarea.Style;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;

import java.awt.*;

import static de.uka.ilkd.key.nparser.KeYLexer.*;

public class KeYLexerSyntaxScheme extends SyntaxScheme {

    public KeYLexerSyntaxScheme() {
        super(true);
    }

    @Override
    public Style getStyle(int index) {
        Style style = new Style();
        Color color;
        switch (index) {
            case IMP:
            case NOT:
            case EQV:
                color = Color.RED;
                break;
            case PROBLEM:
            case PREDICATES:
            case PROFILE:
            case KEYSETTINGS:
            case PROOFOBLIGATION:
            case JAVASOURCE:
            case SORTS:
                color = Color.BLUE;
                break;
            default: color = null;
        }
        if (color != null) {
            style.foreground = color;
        }
        return style;
    }

}
