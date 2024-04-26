package de.uka.ilkd.key.gui.specbrowse;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import org.jspecify.annotations.NonNull;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.util.List;

/**
 *
 * @author Alexander Weigl 
 * @version 1 (26.04.24)
 */
@KeYGuiExtension.Info
public class SpecBrowseExtension implements KeYGuiExtension, KeYGuiExtension.MainMenu {
    @Override
    public @NonNull List<Action> getMainMenuActions(@NonNull MainWindow mainWindow) {
        return List.of(new OpenSpecBrowserWithCurrentProofAction(mainWindow));
    }

    public class OpenSpecBrowserWithCurrentProofAction extends MainWindowAction {
        public OpenSpecBrowserWithCurrentProofAction(MainWindow mw) {
            super(mw);
            setName("Open Specification Browser");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            var specs = mainWindow.getMediator().getSelectedProof().getServices().getSpecificationRepository();
            var browser = new SpecificationBrowser(specs);
            browser.setVisible(true);
        }
    }
}
