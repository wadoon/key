package de.uka.ilkd.key.nui.view.embeddedswingcontent;

import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewControllerSwingContent;
import de.uka.ilkd.key.nui.ViewPosition;

/**
 * Embeds the {@link ProofTreeView Proof Tree View} from the old UI.
 * 
 * @author Nils Muzzulini
 * @version 1.0
 * @see ProofTreeView
 */
@KeYView(title = "Tree", path = "TreeView.fxml", accelerator = "CTRL + T", preferredPosition = ViewPosition.TOPRIGHT)
public class TreeViewController extends ViewControllerSwingContent {

    @Override
    public void createSwingContent() {
        ProofTreeView proofTreeView = new ProofTreeView(getContext().getKeYMediator());
        getSwingNode().setContent(proofTreeView);
    }
}
