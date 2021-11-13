package de.uka.ilkd.key.gui.extensions.explore;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.TacletApp;

import java.awt.event.ActionEvent;

/**
 * @author Alexander Weigl
 * @version 1 (11/13/21)
 */
public class ExplorativeAction extends KeyAction {
    {
        setMenuPath("Explore");
    }

    public ExplorativeAction(TacletApp app) {
        setName(app.rule().displayName());
        setEnabled(2 == app.taclet().goalTemplates().size());
    }


    public ExplorativeAction(BuiltInRule app) {
        setName(app.displayName());
        setEnabled(false);
    }

    @Override
    public void actionPerformed(ActionEvent e) {

    }
}
