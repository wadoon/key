package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.actions.MainWindowAction;

import javax.swing.*;
import java.awt.event.ActionEvent;

/**
 * Created by weigl on 3/24/16.
 */
public class SaveAsHtmlAction extends MainWindowAction {

    public SaveAsHtmlAction(MainWindow mainWindow) {
        super(mainWindow);

        setName("Save As Html");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        JOptionPane.showMessageDialog(this.mainWindow,
                "Currently not Implemented", "Save As Html",JOptionPane.ERROR_MESSAGE);
    }
}
