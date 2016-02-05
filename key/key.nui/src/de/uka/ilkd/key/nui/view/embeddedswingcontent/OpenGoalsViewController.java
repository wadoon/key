package de.uka.ilkd.key.nui.view.embeddedswingcontent;

import javax.swing.JScrollPane;

import de.uka.ilkd.key.gui.GoalList;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewControllerSwingContent;
import de.uka.ilkd.key.nui.ViewPosition;

/**
 * Embeds the Open Goals View from the old UI.
 * 
 * @author Nils Muzzulini
 *
 */
@KeYView(title = "Open Goals", path = "OpenGoalsView.fxml", preferredPosition = ViewPosition.TOPLEFT)
public class OpenGoalsViewController extends ViewControllerSwingContent {

    private JScrollPane openGoalsView;

    @Override
    public void createSwingContent() {
        // set openGoalsView
        openGoalsView = new JScrollPane();
        // GuiUtilities.paintEmptyViewComponent(openGoalsView, "Open Goals");
        GoalList goalList = new GoalList(getContext().getKeYMediator());
        openGoalsView.setViewportView(goalList);

        getSwingNode().setContent(openGoalsView);
    }
}
