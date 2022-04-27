package org.key_project.slicing;

import javax.swing.*;

public class ExportButton extends JButton {
    private final SlicingExtension ext;

    public ExportButton(SlicingExtension ext) {
        super();
        setName("Export DOT");
        this.ext = ext;
    }
}
