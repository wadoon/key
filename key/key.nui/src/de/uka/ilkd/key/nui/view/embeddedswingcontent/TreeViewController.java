package de.uka.ilkd.key.nui.view.embeddedswingcontent;

import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewControllerSwingContent;
import de.uka.ilkd.key.nui.ViewPosition;

/**
 * Embeds the Tree View from the old UI.
 * 
 * @author Nils Muzzulini
 *
 */
@KeYView(title = "Tree", path = "TreeView.fxml", preferredPosition = ViewPosition.TOPLEFT)
public class TreeViewController extends ViewControllerSwingContent {

    @Override
    public void createSwingContent() {
        ProofTreeView proofTreeView = new ProofTreeView(getContext().getProofManager().getMediator());
        getSwingNode().setContent(proofTreeView);
    }
}
