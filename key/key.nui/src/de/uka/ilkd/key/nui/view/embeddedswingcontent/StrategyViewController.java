package de.uka.ilkd.key.nui.view.embeddedswingcontent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.StrategySelectionView;
import de.uka.ilkd.key.gui.actions.AutoModeAction;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewControllerSwingContent;
import de.uka.ilkd.key.nui.ViewPosition;

@KeYView(title = "Proof Search Strategy", path = "StrategyView.fxml", preferredPosition = ViewPosition.TOPLEFT)
public class StrategyViewController extends ViewControllerSwingContent {
    
    private AutoModeAction autoModeAction = new AutoModeAction(MainWindow.getInstance(false));
    
    @Override
    public void createSwingContent() {
        
        final StrategySelectionView strategySelectionView = new StrategySelectionView(autoModeAction);
        strategySelectionView.setMediator(getContext().getProofManager().getMediator());
        
        getSwingNode().setContent(strategySelectionView);
    }

}
