/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import javafx.scene.input.MouseEvent;
import javafx.scene.text.Font;
import javafx.scene.text.Text;

/**
 * @author Maximilian Li
 *
 */
public class PositionConverter {
    // private String proofString;
    private String[] strings;

    /**
     * 
     */
    public PositionConverter(String proofString) {
        // this.proofString = proofString;
        strings = proofString.split("\n");
    }

    /**
     * returns the Character under the MousePointer
     * 
     * @param event
     *            the mouse event
     * @return if no char: -1; else index of the underlying char in the
     *         proofstring.
     */
    public int getCharIdxUnderPointer(MouseEvent event) {
        int idx = -1;
        int row = (int) Math.round((event.getY() - 15.0) / 18.0);

        if (row >= 0 && row < strings.length) {
            int charInRow = getCharIdxInRow(event.getX(), row);

            if (charInRow != -1) {

                idx = getCharIndex(row, charInRow);
                // char c = proofString.charAt(idx);

                /*
                 * System.out.println("Hack Index: " + idx); System.out.println(
                 * "Hack Char at this Pos: " + proofString.charAt(idx));
                 * System.out .println(event.getY() + ", " + event.getX() + ": "
                 * + c);
                 */
            }
        }
        // System.out.println("####");
        return idx;
    }

    /**
     * returns the idx of the char under the mousepointer relative to the row
     * 
     * @param xCoordinate
     *            the x-value of the Mouse event
     * @param row
     *            the row in which the char is located
     * @return the idx of the char inside of the given row
     */
    private int getCharIdxInRow(double xCoordinate, int row) {
        // Adjust for left margin
        double xCord = xCoordinate - 5;
        int result = 0;

        // Generate Text Object with Font and Size for computing width
        Text text = new Text();
        text.setFont(new Font("Courier New", 16));

        // For each char check width
        for (char c : strings[row].toCharArray()) {
            text.setText("" + c);
            xCord -= (text.getLayoutBounds().getWidth());

            if (xCord < 0) {
                break;
            }

            result++;
        }
        // If MousePointer is to the right to end of line, return -1
        if (xCord > 0) {
            return -1;
        }

        /*
         * System.out.println("Graphic Result: " + result); System.out.println(
         * "Graphic ResultString: " + strings[row].charAt(result));
         */
        return result;
    }

    /**
     * gets the Index of a specific Char in the proofString
     * 
     * @param row
     *            the row of the char
     * @param charInRow
     *            the position of the char inside of the row
     * @return returns the index of the char in proofstring
     */
    private int getCharIndex(int row, int charInRow) {
        int idx = 0;
        for (int i = 0; i < row; i++) {
            idx += strings[i].length();
        }
        idx += charInRow + row;

        return idx;
    }

}
