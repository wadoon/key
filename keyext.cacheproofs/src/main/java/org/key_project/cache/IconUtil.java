package org.key_project.cache;

import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFont;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;

import javax.swing.*;
import java.awt.*;

public class IconUtil {
    public static Icon makeDoubleIcon(IconFont icon1, IconFont icon2) {
        Icon i1 = makeIcon(icon1);
        Icon i2 = makeIcon(icon2);
        return new DoubleIcon(i1, i2, 5);
    }

    public static Icon makeIcon(IconFont iconCode) {
        return IconFontSwing.buildIcon(iconCode, 16, Color.BLACK);
    }

    private static class DoubleIcon implements Icon {
        private final Icon icon1;
        private final Icon icon2;
        private final int gap;

        public DoubleIcon(Icon i1, Icon i2, int gap) {
            icon1 = i1;
            icon2 = i2;
            this.gap = gap;
        }

        @Override
        public void paintIcon(Component c, Graphics g, int x, int y) {
            icon1.paintIcon(c, g, x, y);
            icon2.paintIcon(c, g, x + gap + icon1.getIconWidth(), y);
        }

        @Override
        public int getIconWidth() {
            return icon1.getIconWidth() + gap + icon2.getIconWidth();
        }

        @Override
        public int getIconHeight() {
            return Integer.max(icon1.getIconHeight(), icon2.getIconHeight());
        }
    }
}
