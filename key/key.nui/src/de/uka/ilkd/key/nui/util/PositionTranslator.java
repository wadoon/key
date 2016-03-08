/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import java.util.ArrayList;

import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import de.uka.ilkd.key.util.Pair;
import javafx.scene.input.MouseEvent;
import javafx.scene.text.Font;
import javafx.scene.text.Text;

/**
 * @author Maximilian Li
 *
 */
public class PositionTranslator {
    private String[] strings;
    private String font;
    private int fontSize;
    private int minimizedSize;
    private boolean filterCollapsed = false;
    private ArrayList<Integer> filteredLines = new ArrayList<Integer>();
    private CssFileHandler cssHandler;
    private static Font normalFont;
    private static Font minimizedFont;

    /**
     * Creates a PositionTranslator Object, which is able to return the index of
     * the char in the printed proofString under the mousepointer
     */
    public PositionTranslator(CssFileHandler cssFileHandler) {
        cssHandler = cssFileHandler;
        this.readCSS();
    }
    /**
     * Setter for the proofString
     * @param proofString
     */
    public void setProofString(String proofString) {
        strings = proofString.split("\n");
        filteredLines.clear();
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
        this.readCSS();
        // Compute Line
        int line = getLine(event.getY());

        // If valid Line
        if (line != -1 && line < strings.length) {
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
     * 
     * @param yCoordinate
     *            the YCoordinate of the MouseEvent
     * @return the number of the underlying line
     */
    private int getLine(double yCoordinate) {
        double yCoord = yCoordinate - fontSize * 2.0 / 3.0;
        int result;

        Text text = new Text("\\W|QpXgj�&");
        text.setFont(normalFont);
        int collapsedLinesAdjustment = 0;

        for (result = 0; result < strings.length; result++) {

            // Adjust for filtering
            if (filterCollapsed) {
                if (!filteredLines.contains(result)) {
                    if (filteredLines.contains(result + 1)) {
                        yCoord -= Math
                                .round(text.getLayoutBounds().getHeight());
                    }
                    continue;
                }
            }
            else {
                if (!filteredLines.contains(result)
                        && filteredLines.size() > 0) {
                    text.setFont(minimizedFont);
                }
                else {
                    text.setFont(normalFont);
                }
            }
            yCoord -= Math.round(text.getLayoutBounds().getHeight());

            if (yCoord < 0) {
                break;
            }
        }
        result -= collapsedLinesAdjustment;
        if (yCoord > 0 || (filterCollapsed && filteredLines.size() > 0
                && !filteredLines.contains(result))) {
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
        // Adjust for minimized Filter
        if (!filterCollapsed && !filteredLines.contains(line)
                && filteredLines.size() > 0) {
            text.setFont(minimizedFont);
        }
        else {
            text.setFont(normalFont);
        }

        // For each char check width

        for (char c : strings[line].toCharArray()) {
            text.setText(String.valueOf(c));
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

    /**
     * reads the CSS information for HTML Styling from the CSSFileHandler
     * {@link CssFileHandler}
     */
    private void readCSS() {
        CssRule pre = cssHandler.getRule("pre");
        CssRule minimized = cssHandler
                .getRule("." + NUIConstants.FILTER_MINIMIZED_TAG);

        font = pre.getValue("font-family");
        String fontSizeValue = pre.getValue("font-size");

        // FontSize Value ends with "..px"
        fontSize = Integer.parseInt(
                fontSizeValue.substring(0, fontSizeValue.length() - 2));

        fontSizeValue = minimized.getValue("font-size");

        minimizedSize = Integer.parseInt(
                fontSizeValue.substring(0, fontSizeValue.length() - 2));

        normalFont = new Font(font, fontSize);
        minimizedFont = new Font(font, minimizedSize);
    }

    /**
     * gives Information on the Filtering to the PosTranslator
     * 
     * @param lines
     *            the number of lines, which are not filtered out
     * @param layout
     *            the modus (Minimized/Collapsed) of the Filter
     */
    public void applyFilter(ArrayList<Integer> lines, FilterLayout layout) {
        filteredLines = lines;
        switch (layout) {
        case Minimize:
            filterCollapsed = false;
            break;
        case Collapse:
            filterCollapsed = true;
            break;
        default:
            filterCollapsed = false;
            break;
        }
    }

    /**
     * computes dimensions of the proofstring given to the PositionTranslator,
     * if drawn with the Font and Size as defined in the CSS
     * 
     * @return a Pair, with Pair.first = width and Pair.second = height
     */

    public Pair<Double, Double> getProofHeight() { // Adjustment for Margin
        this.readCSS();
        double height = 2 * fontSize;

        Text text = new Text(" ");
        text.setFont(new Font(font, fontSize));
        String longestLine = "";

        // Iterate over all lines to sum up Height
        for (int i = 0; i < strings.length; i++) {
            if (strings[i].length() > longestLine.length()) {
                longestLine = strings[i];
            }
            height += Math.round(text.getLayoutBounds().getHeight());
        }
        text.setText(longestLine);

        return new Pair<Double, Double>(
                (double) Math.round(
                        text.getLayoutBounds().getWidth() + 2 * fontSize),
                height);
    }

}
