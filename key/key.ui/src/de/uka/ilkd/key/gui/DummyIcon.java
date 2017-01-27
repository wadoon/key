package de.uka.ilkd.key.gui;

import javax.swing.*;
import java.awt.*;

/**
 * Dummy icon for change with breakpoint icon
 * Created by sarah on 1/27/17.
 */
public class DummyIcon implements Icon {

    public boolean isDummy() {
        return isDummy;
    }

    private boolean isDummy;

    public DummyIcon(){
        isDummy = true;
    }

    @Override
    public void paintIcon(Component component, Graphics graphics, int i, int i1) {

    }

    @Override
    public int getIconWidth() {
        return 10;
    }

    @Override
    public int getIconHeight() {
        return 10;
    }
}
