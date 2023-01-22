package org.key_project.cache;

import javax.swing.*;
import java.awt.event.ActionEvent;

public class RecordCacheAction extends AbstractAction {
    private final CacheExtension cacheExtension;

    public RecordCacheAction(CacheExtension cacheExtension) {
        putValue(NAME, "Record");
        this.cacheExtension = cacheExtension;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        cacheExtension.recordIntoCache();
    }
}
