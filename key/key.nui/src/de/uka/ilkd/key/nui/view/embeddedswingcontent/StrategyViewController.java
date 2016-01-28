package de.uka.ilkd.key.nui.view.embeddedswingcontent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.StrategySelectionView;
import de.uka.ilkd.key.gui.actions.AutoModeAction;
import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewControllerSwingContent;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.model.AutoModeActionFX;
import de.uka.ilkd.key.nui.model.Context;
import de.uka.ilkd.key.nui.model.StrategySelectionFX;

@KeYView(title = "Proof Search Strategy", path = "StrategyView.fxml", preferredPosition = ViewPosition.TOPLEFT)
public class StrategyViewController extends ViewControllerSwingContent {
    
    //private AutoModeActionFX autoModeAction = new AutoModeActionFX(getContext());
    //private AutoModeAction autoModeAction = new AutoModeAction(MainWindow.getInstance(false));
    
    @Override
    public void createSwingContent() {
        AutoModeActionFX autoModeAction = new AutoModeActionFX(getContext());
        final StrategySelectionFX strategySelectionView = new StrategySelectionFX(autoModeAction);
        //final StrategySelectionView strategySelectionView = new StrategySelectionView(autoModeAction);
        strategySelectionView.setMediator(getContext().getProofManager().getMediator());
        
        getSwingNode().setContent(strategySelectionView);
    }
    public StrategyViewController() {
        //System.out.println(getContext());
    }

}
