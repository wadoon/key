/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.nui.model.PrintFilter;
import javafx.scene.input.MouseEvent;
import javafx.scene.text.Font;
import javafx.scene.text.Text;

/**
 * @author Maximilian Li
 *
 */
public class PositionTranslator {
    private String[] strings;
    private String cssPath;
    private String proofString;
    private String font;
    private int fontSize;
    private int minimizedSize;
    private boolean filterCollapsed = false;
    private boolean filterInverted = false;
    private ArrayList<Integer> filteredLines = new ArrayList<Integer>();

    /**
     * 
     */
    public PositionTranslator(String cssPath) {
        try {
            readCSS(cssPath);
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        finally {
            this.cssPath = cssPath;
        }
    }

    public void setProofString(String proofString) {
        this.proofString = proofString;
        strings = proofString.split("\n");
        try {
            readCSS(cssPath);
        }
        catch (IOException e) {
            e.printStackTrace();
        }
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
     * 
     * @param yCoordinate
     *            the YCoordinate of the MouseEvent
     * @return the number of the underlying line
     */
    private int getLine(double yCoordinate) {
        double yCoord = yCoordinate - 5;
        int result;

        Text text = new Text(" ");
        text.setFont(new Font(font, fontSize));
        for (result = 0; result < strings.length; result++) {
            // Adjust for filtering
            if (filteredLines.contains(result) != filterInverted) {
                if (filterCollapsed) {
                    continue;
                }
            }
            yCoord -= text.getLayoutBounds().getHeight();

            if (yCoord < 0) {
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
        // Adjust for minimized Filter
        if (!filterCollapsed
                && (filteredLines.contains(line) != filterInverted)) {
            text.setFont(new Font(font, minimizedSize));
        }
        else {
            text.setFont(new Font(font, fontSize));
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
     * reads the CSS information for HTML Styling
     * 
     * @param fileName
     *            path to the CSS file
     * @throws IOException
     */
    private void readCSS(String fileName) throws IOException {
        BufferedReader br = new BufferedReader(new FileReader(fileName));
        try {
            String line = br.readLine();

            boolean inPre = false;
            boolean inMinimized = false;
            while (line != null) {
                // Set the Font Style and Family Information used in <Pre> Block
                if (inPre) {
                    if (line.startsWith("}")) {
                        inPre = false;
                    }
                    else if (line.contains("font-family")) {
                        font = line.split("\"")[1];
                    }
                    else if (line.contains("font-size")) {
                        Pattern pattern = Pattern.compile("[0-9]+");
                        Matcher matcher = pattern.matcher(line);
                        matcher.find();
                        fontSize = Integer.parseInt(matcher.group());
                    }
                }
                //Set the Font Size Informotion used in .minimized Style Class
                else if (inMinimized) {
                    if (line.startsWith("}")) {
                        inMinimized = false;
                    }
                    else if (line.contains("font-size")) {
                        Pattern pattern = Pattern.compile("[0-9]+");
                        Matcher matcher = pattern.matcher(line);
                        matcher.find();
                        minimizedSize = Integer.parseInt(matcher.group());
                    }
                }
                else if (line.startsWith("pre{")) {
                    inPre = true;
                }
                else if (line.startsWith(".minimized{")) {
                    inMinimized = true;
                }

                line = br.readLine();
            }
        }
        finally {
            br.close();
        }
    }
    /**
     * apply Filter information on the PositionTranslator.
     * @param filter the PrintFilter object
     */
    public void applyFilter(PrintFilter filter) {
        filteredLines = SequentFilterer.ApplyFilter(proofString, filter);
        // XXX
        filterCollapsed = false;
        filterInverted = filter.getInvert();
    }
}
