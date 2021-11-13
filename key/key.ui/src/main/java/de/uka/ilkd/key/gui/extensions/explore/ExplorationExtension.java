package de.uka.ilkd.key.gui.extensions.explore;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.DefaultContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.nodeviews.CurrentGoalViewMenu;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.TacletApp;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (11/13/21)
 */
@KeYGuiExtension.Info(name = "Explorative Sideproof Rules",
        optional = true,
        experimental = false,
        description = "Allows to do stuff...",
        priority = 10000)
public class ExplorationExtension implements
        KeYGuiExtension,
        KeYGuiExtension.ContextMenu {
    @Override
    public @Nonnull
    List<Action> getContextActions(@Nonnull KeYMediator mediator,
                                   @Nonnull ContextMenuKind kind,
                                   @Nonnull Object underlyingObject) {
        if (kind == DefaultContextMenuKind.GOAL_VIEW) {
            CurrentGoalViewMenu.GoalViewData data = (CurrentGoalViewMenu.GoalViewData) underlyingObject;
            var s1 = data.toAdd.stream().map(this::createRuleApplication);
            var s2 = data.builtInList.stream().map(this::createRuleApplication);
            return Stream.concat(s1, s2).collect(Collectors.toList());
        }
        return Collections.emptyList();
    }

    private Action createRuleApplication(TacletApp app) {
        return new ExplorativeAction(app);
    }

    private Action createRuleApplication(BuiltInRule app) {
        return new ExplorativeAction(app);
    }
}
