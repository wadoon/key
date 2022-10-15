package de.uka.ilkd.key.gui.rsta;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;

import rsta.InputDisplay;
import rsta.TextEditor;

import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;

public class EditorAction extends MainWindowAction {

    private Class<?> grammarClass;
    private String input;

    private Dialog parent;

    public EditorAction(Class<?> grammarClass, String input, MainWindow window, Dialog parent) {
        super(window);
        this.input = input;
        this.grammarClass = grammarClass;
        this.parent = parent;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        TextEditor editor = InputDisplay.display(input, grammarClass, parent);
        editor.setVisible(true);
    }
}
