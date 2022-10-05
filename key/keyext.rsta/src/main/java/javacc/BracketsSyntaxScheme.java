package javacc;

import org.fife.ui.rsyntaxtextarea.Style;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;

import java.awt.*;

public class BracketsSyntaxScheme extends SyntaxScheme {

    public BracketsSyntaxScheme() {
        super(true);
    }

    @Override
    public Style getStyle(int index) {
        Style style = new Style();
        Color color;
        switch (index) {
            case javacc.BracketsConstants.RBRACKET:
                color = Color.MAGENTA;
                break;
            case javacc.BracketsConstants.LBRACKET:
                color = Color.BLUE;
                break;
            case javacc.BracketsConstants.NO_MATCH:
                    style.underline = true;
                    color = Color.RED;
                    break;
            default: color = Color.BLACK;
        }
        if (color != null) {
            style.foreground = color;
        }
        return style;
    }

}