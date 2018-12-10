/**
 * 
 */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
// import java.awt.event.KeyEvent;
import java.io.File;

import javax.swing.SwingUtilities;
import javax.swing.ToolTipManager;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;

/**
 * @author Michael Kirsten
 *
 */
public final class ReloadCurrentProofAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    public ReloadCurrentProofAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Reload Current Proof");
        setIcon(IconFactory.reloadCurrent(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Reload current proof.");
        // setAcceleratorLetter(KeyEvent.VK_C);
        mainWindow.getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (getMediator().getSelectedProof() != null
                && getMediator().getSelectedProof().getProofFile() != null) {
            Proof oldProof = getMediator().getSelectedProof();
            final String currentFile =
                    getMediator().getSelectedProof().getProofFile().getAbsolutePath();
            if (currentFile != null) {
                // Abandon old proof
                final boolean removalConfirmed = true;
                // TODO: Maybe one wants a confirmation question?
                synchronized (oldProof) {
                    if (removalConfirmed) {
                        oldProof.dispose();
                        oldProof = null;
                    }
                }

                final File file = new File(currentFile);
                final KeYFileChooser fileChooser =
                        KeYFileChooser.getFileChooser("Select file to load proof or problem");
                fileChooser.selectFile(file);
                mainWindow.loadProblem(file);
            }
        }
    }

}
