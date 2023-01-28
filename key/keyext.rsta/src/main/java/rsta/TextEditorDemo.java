package rsta;

import javacc.TestCC;
import testlexer.Testlexer;
import testlexer.Testlexer_Inner;

import javax.swing.*;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class TextEditorDemo {

    private static final long serialVersionUID = 1L;

    private static final String inputFile = "testlexer.txt";
    private static final List<Class<?>> lexerClasses = new ArrayList<>();

    private static final Map<Class<?>, Map<String, Class<?>>> map = new HashMap<>();

    public static void main(String[] args) {
        /*lexerClasses.add(TestCC.class);
        Map<String, Class<?>> innerMap = new HashMap<>();
        map.put(TestCC.class, innerMap);*/
        lexerClasses.add(Testlexer.class);
        lexerClasses.add(Testlexer_Inner.class);
        Map<String, Class<?>> innerMap = new HashMap<>();
        innerMap.put("TEST", Testlexer_Inner.class);
        map.put(Testlexer.class, innerMap);
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
                TextEditor editor = InputDisplay.display(text.toString(), new JDialog(), lexerClasses, map);
                editor.addWindowListener(new WindowAdapter() {
                    @Override
                    public void windowClosed(WindowEvent e) {
                        System.exit(0);
                    }
                });
                editor.setVisible(true);
            }
        });
    }

}

