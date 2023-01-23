package org.key_project.cache;

import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;

import javax.swing.*;
import java.awt.event.ActionEvent;

public class EmptyProofCachesAction extends AbstractAction {
    private final CacheExtension cacheExtension;


    public EmptyProofCachesAction(CacheExtension cacheExtension) {
        putValue(SHORT_DESCRIPTION, "Empty the proof node cache");
        putValue(LARGE_ICON_KEY, IconUtil.makeIcon(FontAwesomeSolid.TRASH_ALT));
        this.cacheExtension = cacheExtension;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        cacheExtension.clearCache();
    }
}
