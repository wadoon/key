package org.key_project.cache;

import javax.swing.*;
import java.awt.event.ActionEvent;

public class ToggleProofCacheAction extends AbstractAction {
    private final CacheExtension cacheExtension;

    public ToggleProofCacheAction(CacheExtension cacheExtension) {
        putValue(NAME, "Toggle the caching mechanism");
        this.cacheExtension = cacheExtension;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        cacheExtension.setEnabled(Boolean.TRUE == getValue(SELECTED_KEY));
    }
}
