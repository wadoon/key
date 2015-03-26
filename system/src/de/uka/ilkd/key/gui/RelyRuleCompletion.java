package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RelyBuiltInRuleApp;
import de.uka.ilkd.key.rule.RelyRule;

// TODO: Remove after transformation
public class RelyRuleCompletion implements InteractiveRuleApplicationCompletion {

    @Override
    public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
        if (!app.complete() && ((RelyBuiltInRuleApp) app).cannotComplete(goal)) {
            return app;
        }
        if (forced) {
            app = app.tryToInstantiate(goal);
            if (app.complete()) {
                return app;
            }
        }
        return null; // TODO: interactive completion
    }

    @Override
    public boolean canComplete(IBuiltInRuleApp app) {
        return checkCanComplete(app);
    }

    /**
     * Checks if the app is supported.
     * This functionality is also used by the Eclipse plug-ins like the KeYIDE.
     */
    public static boolean checkCanComplete(final IBuiltInRuleApp app) {
        return app.rule() instanceof RelyRule;
    }
}
