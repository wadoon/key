/**
 * 
 */
package playground.richtextFX.util;

import javafx.scene.text.Text;

/**
 * @author Maximilian Li
 *
 */
public class CustomText extends Text {
    int index;

    /**
     * 
     */
    public CustomText() {
        // TODO Auto-generated constructor stub
    }

    /**
     * @param text
     */
    public CustomText(String text, int index) {
        super(text);
        index = index;
        // TODO Auto-generated constructor stub
    }
    public int getIndex(){
        return index;
    }
    /**
     * @param x
     * @param y
     * @param text
     */
    public CustomText(double x, double y, String text) {
        super(x, y, text);
        // TODO Auto-generated constructor stub
    }

}
