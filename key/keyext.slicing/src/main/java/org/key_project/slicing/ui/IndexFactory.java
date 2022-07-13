package org.key_project.slicing.ui;

public class IndexFactory {
    private int idx = 0;

    public int nextIndex() {
        return idx++;
    }
}
