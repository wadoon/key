package de.uka.ilkd.key.nui.view.embeddedswingcontent;

import de.uka.ilkd.key.nui.KeYView;
import de.uka.ilkd.key.nui.ViewControllerSwingContent;
import de.uka.ilkd.key.nui.ViewPosition;
import de.uka.ilkd.key.nui.util.embeddedswingcontent.AutoModeActionFX;
import de.uka.ilkd.key.nui.util.embeddedswingcontent.StrategySelectionFX;

@KeYView(title = "Proof Search Strategy", path = "StrategyView.fxml", preferredPosition = ViewPosition.TOPLEFT)
public class StrategyViewController extends ViewControllerSwingContent {

    @Override
    public void createSwingContent() {
        AutoModeActionFX autoModeAction = new AutoModeActionFX(getContext());
        final StrategySelectionFX strategySelectionFX = new StrategySelectionFX(autoModeAction);
        strategySelectionFX.setMediator(getContext().getProofManager().getMediator());

        getSwingNode().setContent(strategySelectionFX);
    }
}
