package antlr;

import org.fife.ui.rsyntaxtextarea.Style;
import org.fife.ui.rsyntaxtextarea.SyntaxScheme;

import java.awt.*;

public class JmlLexerSyntaxScheme extends SyntaxScheme {

    public JmlLexerSyntaxScheme() {
        super(true);
    }

    @Override
    public Style getStyle(int index) {
        Style style = new Style();
        Color color;
        switch (index) {
            default: color = Color.BLUE;
        }
        if (color != null) {
            style.foreground = color;
        }
        return style;
    }

}
