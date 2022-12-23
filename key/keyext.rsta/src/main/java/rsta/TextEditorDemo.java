package rsta;

import de.uka.ilkd.key.nparser.KeYLexer;
import lexerFactories.VariousGrammarsSyntaxSchemeFactory;

import javax.swing.*;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class TextEditorDemo {

    private static final long serialVersionUID = 1L;

    private static final String inputFile = "contraposition.txt";
    private static final List<Class<?>> lexerClasses = Collections.singletonList(KeYLexer.class);

    private static final Map<Class<?>, Map<String, Class<?>>> map = new HashMap<>();

    public static void main(String[] args) {
        // Start all Swing applications on the EDT.
        InputStream inputStream = TextEditorDemo.class.getResourceAsStream(inputFile);
        BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream));
        StringBuilder text = new StringBuilder();
        try {
            while (reader.ready()) {
                text.append(reader.readLine() + '\n');
            }
        } catch (IOException e) {
            e.printStackTrace();
        }

        SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
                InputDisplay.display(text.toString(), new JDialog(), lexerClasses, map).setVisible(true);
            }
        });
    }

}

