/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import org.stringtemplate.v4.compiler.CodeGenerator.primary_return;

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
        // Compute Line
        int line = getLine(event.getY());
        
        // If valid Line
        if (line != -1) {
            // Get Position of the Char under MousePointer in this specific Line
            int charPosInLine = getCharIdxInLine(event.getX(), line);

            // If to the right of last char in Line, return last char (-2
            // adjustment for linebreak)
            if (charPosInLine == -1) {
                return getCharIndex(line, strings[line].length() - 2);
            }
            else {
                return getCharIndex(line, charPosInLine);
            }
        }
        return -1;
    }
    /**
     * uses the Y-Coordinate of MouseEvent to compute underlying line
     * @param yCoordinate the YCoordinate of the MouseEvent
     * @return the number of the underlying line
     */
    private int getLine(double yCoordinate){
        double yCoord = yCoordinate -5;
        int result;
        
        Text text = new Text(" ");
        text.setFont(new Font("Courier New", 16));
        
        for (result = 0; result < strings.length; result++) {
            yCoord -= text.getLayoutBounds().getHeight();
            
            if(yCoord < 0){
                break;
            }
        }
        
        if (yCoord > 0) {
            return -1;
        }

        return result;
    }

    /**
     * returns the idx of the char under the mousepointer relative to the line
     * 
     * @param xCoordinate
     *            the x-value of the Mouse event
     * @param line
     *            the line in which the char is located
     * @return the idx of the char inside of the given line
     */
    private int getCharIdxInLine(double xCoordinate, int line) {
        // Adjust for left margin
        double xCoord = xCoordinate - 5;
        int result = 0;

        // Generate Text Object with Font and Size for computing width
        Text text = new Text();
        text.setFont(new Font("Courier New", 16));

        // For each char check width
        for (char c : strings[line].toCharArray()) {
            text.setText("" + c);
            xCoord -= text.getLayoutBounds().getWidth();

            if (xCoord < 0) {
                break;
            }

            result++;
        }
        // If MousePointer is to the right to end of line, return -1
        if (xCoord > 0) {
            return -1;
        }

        return result;
    }

    /**
     * gets the Index of a specific Char in the proofString
     * 
     * @param line
     *            the line of the char
     * @param charInLine
     *            the position of the char inside of the line
     * @return returns the index of the char in proofstring
     */
    private int getCharIndex(int line, int charPosInLine) {
        int idx = 0;
        // ++ length of lines before
        for (int i = 0; i < line; i++) {
            idx += strings[i].length();
        }
        // ++ position of char in line; ++ (number of linebreaks) == line
        idx += charPosInLine + line;

        return idx;
    }

}
