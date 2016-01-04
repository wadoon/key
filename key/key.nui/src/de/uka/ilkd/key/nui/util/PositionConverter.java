/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import javafx.scene.input.MouseEvent;

/**
 * @author Maximilian Li
 *
 */
public class PositionConverter {
    private String proofString;
    private String[] strings;

    /**
     * 
     */
    public PositionConverter(String proofString) {
        proofString = proofString;
        strings = proofString.split("\n");
    }

    public void takeMouseEvent(MouseEvent event) {
        int row = (int) Math.round((event.getY() -15.0)/ 18.0);
        int charInRow = (int) Math.round((event.getX()- 10) /9.6);
        if (row >= 0 && row < strings.length && charInRow >= 0 && charInRow < strings[row].length()) {
            System.out.println(event.getY() + ", " + event.getX() + ": " + strings[row].charAt(charInRow));
        }
    }

}
