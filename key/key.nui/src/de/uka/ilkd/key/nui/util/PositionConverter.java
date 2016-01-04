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
        this.proofString = proofString;
        strings = proofString.split("\n");
    }

    /**
     * takes a MouseEvent and computes proofChar with MouseEvent Position
     * 
     * @param event
     */
    public void takeMouseEvent(MouseEvent event) {
        int row = (int) Math.round((event.getY() - 15.0) / 18.0);
        int charInRow = (int) Math.round((event.getX() - 10) / 9.6);

        if (row >= 0 && row < strings.length && charInRow >= 0
                && charInRow < strings[row].length()) {

            int idx = getCharIndex(row, charInRow);
            char c = strings[row].charAt(charInRow);

            System.out.println("Index: " + idx);
            System.out.println("Char at this Pos: " + proofString.charAt(idx));
            System.out.println(event.getY() + ", " + event.getX() + ": " + c);

        }
        System.out.println("####");
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
