package de.uka.ilkd.key.nui.view.embeddedswingcontent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.StrategySelectionView;
import de.uka.ilkd.key.gui.actions.AutoModeAction;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewControllerSwingContent;
import de.uka.ilkd.key.nui.ViewPosition;

@KeYView(title = "Proof Search Strategy", path = "StrategyView.fxml", preferredPosition = ViewPosition.TOPLEFT)
public class StrategyViewController extends ViewControllerSwingContent {

    @Override
    public void createSwingContent() {
        StrategySelectionView strategySelectionView = new StrategySelectionView(
                new AutoModeAction(MainWindow.getInstance(false)));
        strategySelectionView.setMediator(getContext().getProofManager().getMediator());
        getSwingNode().setContent(strategySelectionView);
    }

}
