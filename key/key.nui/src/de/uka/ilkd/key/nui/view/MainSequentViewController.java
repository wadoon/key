package de.uka.ilkd.key.nui.view;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewController;
import de.uka.ilkd.key.nui.ViewPosition;
import javafx.application.Platform;
import javafx.fxml.FXML;

/**
 * ViewController for the main sequent view. This view resembles the sequent
 * view of the old UI. It embeds a {@link SequentViewController} and updates it
 * for various events.
 * 
 * @author Victor Schuemmer
 * @version 1.0
 */
@KeYView(title = "Main Sequent", path = "MainSequentView.fxml", accelerator = "SHORTCUT + M", preferredPosition = ViewPosition.CENTER)
public class MainSequentViewController extends ViewController {

    @FXML
    private SequentViewController sequentViewController;

    @Override
    public void initializeAfterLoadingFxml() {
        sequentViewController.initViewController(getMainApp(), getContext());

        KeYSelectionListener proofChangeListener = new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                getContext().getSequentHtmlChangedEvent()
                        .addHandler(eventArgs -> {
                    if (!getContext().getKeYMediator().ensureProofLoaded()) {
                        sequentViewController.clearWebView();
                    }
                });
            }

            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                // execute ui update on javafx thread
                showSequent();
            }
        };

        getContext().getKeYMediator()
                .addKeYSelectionListener(proofChangeListener);

        if (getContext().getKeYMediator().ensureProofLoaded()) {
            showSequent();
        }
    }

    /**
     * loads the currently selected Sequent into the SequentView
     */
    private void showSequent() {
        Platform.runLater(() -> {
            sequentViewController.loadNodeToView(
                    getContext().getKeYMediator().getSelectedGoal(),
                    getContext().getKeYMediator().getSelectedNode());
        });
    }

}
