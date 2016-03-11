/**
 * 
 */
package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.application.Platform;
import javafx.fxml.FXML;

/**
 * @author Victor Schuemmer
 *
 */
@KeYView(title = "Main Sequent", path = "MainSequentView.fxml", preferredPosition = ViewPosition.CENTER, hasMenuItem = true)
public class MainSequentViewController extends ViewController {

    @FXML
    private SequentViewController sequentViewController;

    @Override
    public void initializeAfterLoadingFxml() {
        sequentViewController.setMainApp(getMainApp(), getContext());

        KeYSelectionListener proofChangeListener = new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
            }

            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                // execute ui update on javafx thread
                Platform.runLater(() -> {
                    sequentViewController.loadProofToView(
                            getContext().getKeYMediator().getSelectedNode());
                                   });
            }
        };

        getContext().getKeYMediator()
                .addKeYSelectionListener(proofChangeListener);
    }

}
