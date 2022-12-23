package de.uka.ilkd.key.gui.rsta;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;

import lexerFactories.VariousGrammarsSyntaxSchemeFactory;
import rsta.InputDisplay;
import rsta.TextEditor;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.util.List;
import java.util.Map;

public class EditorAction extends MainWindowAction {

    private List<Class<?>> lexerClasses;

    private Map<Class<?>, Map<String, Class<?>>> map;
    private String input;

    private Dialog parent;

    public EditorAction(String input, MainWindow window, Dialog parent,
                        List<Class<?>> lexerClasses,
                        Map<Class<?>, Map<String, Class<?>>> map) {
        super(window);
        this.input = input;
        this.parent = parent;
        this.map = map;
        this.lexerClasses = lexerClasses;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        TextEditor editor = InputDisplay.display(input, parent, lexerClasses, map);
        editor.setVisible(true);
    }
}
