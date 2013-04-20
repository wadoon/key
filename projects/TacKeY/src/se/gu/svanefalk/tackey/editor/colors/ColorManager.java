package se.gu.svanefalk.tackey.editor.colors;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

public enum ColorManager {
    INSTANCE;

    private final Map<RGB, Color> colorMapping = new HashMap<RGB, Color>();

    /**
     * Disposes of the color manager by disposing of all mapped colors.
     */
    public void dispose() {
        for (final Color color : this.colorMapping.values()) {
            color.dispose();
        }
    }

    /**
     * Get the {@link Color} instance corresponding to a given {@link RGB}
     * value.
     * 
     * @param rgb
     *            the RGB valuse
     * @return the Color instance
     */
    public Color getColor(final RGB rgb) {
        Color color = this.colorMapping.get(rgb);

        /*
         * If the color is not already mapped, lazily instantiate it.
         */
        if (color == null) {
            color = new Color(Display.getCurrent(), rgb);
            this.colorMapping.put(rgb, color);
        }
        return color;
    }
}