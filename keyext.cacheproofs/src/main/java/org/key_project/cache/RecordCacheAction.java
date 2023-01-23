package org.key_project.cache;

import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;

import javax.swing.*;
import java.awt.event.ActionEvent;

public class RecordCacheAction extends AbstractAction {
    private final CacheExtension cacheExtension;

    public RecordCacheAction(CacheExtension cacheExtension) {
        putValue(SHORT_DESCRIPTION, "Record the closed nodes of the current proof into the cache");
        putValue(LARGE_ICON_KEY, IconUtil.makeIcon(FontAwesomeSolid.DOWNLOAD));
        this.cacheExtension = cacheExtension;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        cacheExtension.recordIntoCache();
    }
}
