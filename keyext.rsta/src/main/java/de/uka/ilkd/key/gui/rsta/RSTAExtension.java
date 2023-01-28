package de.uka.ilkd.key.gui.rsta;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import lexerFactories.VariousGrammarsSyntaxSchemeFactory;
import rsta.InputDisplay;

import javax.swing.*;
import java.awt.*;
import java.util.List;
import java.util.Map;

@KeYGuiExtension.Info(name = "RSTAExtension",
        experimental = false,
        description = "keyext.rsta")
public class RSTAExtension implements KeYGuiExtension, KeYGuiExtension.EditorExtension {

    public RSTAExtension() {

    }

    @Override
    public MainWindowAction getEditorAction(String input, MainWindow window, Dialog parent,
                                            List<Class<?>> lexerClasses,
                                            Map<Class<?>, Map<String, Class<?>>> map) {
        return new EditorAction(input, window, parent, lexerClasses, map);
    }

    @Override
    public Component getPanel(List<Class<?>> lexerClasses, Map<Class<?>, Map<String, Class<?>>> map, String input, Dialog parent) {
        return InputDisplay.panel(input, lexerClasses, map, parent);
    }
}
