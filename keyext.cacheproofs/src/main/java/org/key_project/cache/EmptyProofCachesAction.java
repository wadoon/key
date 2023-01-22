package org.key_project.cache;

import javax.swing.*;
import java.awt.event.ActionEvent;

public class EmptyProofCachesAction extends AbstractAction {
    private final CacheExtension cacheExtension;


    public EmptyProofCachesAction(CacheExtension cacheExtension) {
        putValue(NAME, "Empty the cache");
        this.cacheExtension = cacheExtension;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        cacheExtension.clearCache();
    }
}
