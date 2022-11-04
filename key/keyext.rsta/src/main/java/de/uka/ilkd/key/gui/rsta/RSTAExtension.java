package de.uka.ilkd.key.gui.rsta;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import rsta.InputDisplay;

import javax.swing.*;
import java.awt.*;

@KeYGuiExtension.Info(name = "RSTAExtension",
        experimental = false,
        description = "keyext.rsta")
public class RSTAExtension implements KeYGuiExtension, KeYGuiExtension.EditorExtension {

    public RSTAExtension() {

    }

    @Override
    public MainWindowAction getEditorAction(Class<?> grammarClass, String input, MainWindow window, Dialog parent) {
        return new EditorAction(grammarClass, input, window, parent);
    }

    @Override
    public Component getPanel(Class<?> grammarClass, String input, Dialog parent) {
        return InputDisplay.panel(input, grammarClass, parent);
    }
}
