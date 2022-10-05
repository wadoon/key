package antlr;

import org.fife.ui.rsyntaxtextarea.Style;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;

import java.awt.*;

import static antlr.BracketsLexer.*;

public class BracketsSyntaxScheme extends SyntaxScheme {

    public BracketsSyntaxScheme() {
        super(true);
    }

    @Override
    public Style getStyle(int index) {
        Style style = new Style();
        Color color;
        switch (index) {
            case LBRACKET:
                color = Color.BLUE;
                break;
            case RBRACKET:
                color = Color.MAGENTA;
                break;
            case NO_MATCH:
                color = Color.RED;
                style.underline = true;
                break;
            default:
                color = Color.BLACK;
        }
        if (color != null) {
            style.foreground = color;
        }
        return style;
    }

}
