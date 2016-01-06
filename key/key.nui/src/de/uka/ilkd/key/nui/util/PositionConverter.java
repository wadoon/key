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
    private String[] strings;

    /**
     * 
     */
    public PositionConverter(String proofString) {
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
        // Approximate Row. TODO: Different Sizes
        int row = (int) Math.round((event.getY() - 15.0) / 18.0);
        // If valid Row
        if (row >= 0 && row < strings.length) {
            // Get Position of the Char under MousePointer in this specific row
            int charPosInRow = getCharIdxInRow(event.getX(), row);

            // If to the right of last char in row, return last char (-2
            // adjustment for linebreak)
            if (charPosInRow == -1) {
                return getCharIndex(row, strings[row].length() - 2);
            }
            else {
                return getCharIndex(row, charPosInRow);
            }
        }
        return -1;
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
    private int getCharIndex(int row, int charPosInRow) {
        int idx = 0;
        // ++ length of rows before
        for (int i = 0; i < row; i++) {
            idx += strings[i].length();
        }
        // ++ position of char in row; ++ (number of linebreaks) == row
        idx += charPosInRow + row;

        return idx;
    }

}
