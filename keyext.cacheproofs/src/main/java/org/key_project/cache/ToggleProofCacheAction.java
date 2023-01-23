package org.key_project.cache;

import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;

import javax.swing.*;
import java.awt.event.ActionEvent;

public class ToggleProofCacheAction extends AbstractAction {
    private final CacheExtension cacheExtension;

    public ToggleProofCacheAction(CacheExtension cacheExtension) {
        putValue(SHORT_DESCRIPTION, "Toggle the caching mechanism");
        putValue(LARGE_ICON_KEY, IconUtil.makeIcon(FontAwesomeSolid.TOGGLE_ON));
        putValue(SELECTED_KEY, Boolean.TRUE);
        this.cacheExtension = cacheExtension;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean enabled = Boolean.TRUE == getValue(SELECTED_KEY);
        cacheExtension.setEnabled(enabled);
    }
}
