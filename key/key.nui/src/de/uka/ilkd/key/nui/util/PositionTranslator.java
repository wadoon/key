package de.uka.ilkd.key.nui.util;

import java.util.ArrayList;

import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import de.uka.ilkd.key.util.Pair;
import javafx.scene.input.MouseEvent;
import javafx.scene.text.Font;
import javafx.scene.text.Text;

/**
 * Provides Functionalities to Translate a Pixel-Position to a Char in the
 * ProofString and vice versa.
 * 
 * @author Maximilian Li
 * @version 1.0
 */
public class PositionTranslator {
    private String[] lines;
    private String font;
    private int fontSize;
    private int minimizedSize;
    private boolean filterCollapsed = false;
    private ArrayList<Integer> unfilteredLines = new ArrayList<Integer>();
    private CssFileHandler cssHandler;
    private static Font normalFont;
    private static Font minimizedFont;

    /**
     * Creates a PositionTranslator Object which is able to return the index of
     * the char in the printed proofString under the mouse pointer.
     * 
     * @param cssFileHandler
     *            {@link CssFileHandler}
     */
    public PositionTranslator(CssFileHandler cssFileHandler) {
        cssHandler = cssFileHandler;
        this.readCSS();
    }

    /**
     * Setter for the proofString.
     * 
     * @param proofString
     *            proofString to be set
     */
    public void setProofString(String proofString) {
        lines = proofString.split("\n");
        unfilteredLines.clear();
    }

    /**
     * Returns the {@link Character} under the mouse pointer.
     * 
     * @param event
     *            the mouse event
     * @return if no char: -1; else index of the underlying char in the proof
     *         string.
     */
    public int getCharIdxUnderPointer(MouseEvent event) {
        this.readCSS();
        // Compute Line
        int line = getLine(event.getY());

        // If valid Line
        if (line != -1 && line < lines.length) {
            // Get Position of the Char under MousePointer in this specific Line
            int charPosInLine = getCharIdxInLine(event.getX(), line);

            // If to the right of last char in Line, return last char (-2
            // adjustment for linebreak)
            if (charPosInLine == -1) {
                return getCharIndex(line, lines[line].length() - 2);
            }
            else {
                return getCharIndex(line, charPosInLine);
            }
        }
        return -1;
    }

    /**
     * Uses the Y-Coordinate of {@link MouseEvent} to compute underlying line.
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

        for (result = 0; result < lines.length; result++) {

            // Adjust for filtering
            if (filterCollapsed) {
                if (!unfilteredLines.contains(result)) {
                    if (unfilteredLines.contains(result + 1)) {
                        yCoord -= Math
                                .round(text.getLayoutBounds().getHeight());
                    }
                    continue;
                }
            }
            else {
                if (!unfilteredLines.contains(result)
                        && unfilteredLines.size() > 0) {
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
        if (yCoord > 0 || (filterCollapsed && unfilteredLines.size() > 0
                && !unfilteredLines.contains(result))) {
            return -1;
        }
        return result;
    }

    /**
     * Returns the index of the {@link Character} under the mouse pointer
     * relative to the line.
     * 
     * @param xCoordinate
     *            the x-value of the Mouse event
     * @param line
     *            the line in which the char is located
     * @return the index of the char inside of the given line
     */
    private int getCharIdxInLine(double xCoordinate, int line) {
        // Adjust for left margin
        double xCoord = xCoordinate - 5;
        int result = 0;

        // Generate Text Object with Font and Size for computing width
        Text text = new Text();
        // Adjust for minimized Filter
        if (!filterCollapsed && !unfilteredLines.contains(line)
                && unfilteredLines.size() > 0) {
            text.setFont(minimizedFont);
        }
        else {
            text.setFont(normalFont);
        }

        // For each char check width

        for (char c : lines[line].toCharArray()) {
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
     * Gets the index of a specific {@link Character} in the proof string.
     * 
     * @param line
     *            the line of the char
     * @param charInLine
     *            the position of the char inside of the line
     * @return returns the index of the char in proof string
     */
    private int getCharIndex(int line, int charPosInLine) {
        int idx = 0;
        // ++ length of lines before
        for (int i = 0; i < line; i++) {
            idx += lines[i].length();
        }
        // ++ position of char in line; ++ (number of linebreaks) == line
        idx += charPosInLine + line;

        return idx;
    }

    /**
     * Reads the CSS information for HTML Styling from the
     * {@link CssFileHandler}.
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
     * Gives information on the filtering to the {@link PositionTranslator}.
     * 
     * @param lines
     *            the number of lines, which are not filtered out
     * @param layout
     *            the modus (Minimized/Collapsed) of the Filter
     */
    public void applyFilter(ArrayList<Integer> lines, FilterLayout layout) {
        unfilteredLines = lines;
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
     * Computes dimensions of the proof string given to the
     * {@link PositionTranslator}, if drawn with the Font and Size as defined in
     * the CSS.
     * 
     * @return a Pair, with Pair.first = width and Pair.second = height
     */

    public Pair<Double, Double> getProofDimensions() {
        this.readCSS();
        // Adjustment for Margin
        double height = 50;

        Text text = new Text(" ");
        text.setFont(new Font(font, fontSize));
        String longestLine = "";

        // Iterate over all lines to sum up Height
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].length() > longestLine.length()) {
                longestLine = lines[i];
            }
            height += Math.round(text.getLayoutBounds().getHeight());
        }
        text.setText(longestLine);

        return new Pair<Double, Double>(
                (double) Math.round(text.getLayoutBounds().getWidth() + 50),
                height);
    }

    /**
     * returns the Height for the char in the proofstring defined by its index
     * position
     * 
     * @param index
     *            the position of the char in the proofstring
     * @return the Height in px
     */
    public Double getHeightForIndex(int index) {
        double height = 5.0;
        int stringIndex = 0;

        Text text = new Text("\\W|QpXgj�&");
        text.setFont(normalFont);

        for (int i = 0; i < lines.length; i++) {
            if (stringIndex >= index) {
                if (filterCollapsed && !unfilteredLines.contains(i - 1)) {
                    return -1.0;
                }
                break;
            }
            if (!unfilteredLines.contains(i)) {
                if (filterCollapsed) {
                    continue;
                }
                else {
                    text.setFont(minimizedFont);
                }
            }
            else {
                text.setFont(normalFont);
            }
            height += text.getLayoutBounds().getHeight();
            stringIndex += lines[i].length() + 1;
        }

        return height;
    }

}
