/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.pp.PositionTable;
import de.uka.ilkd.key.pp.Range;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 *
 */
public class SequentPrinter {
    private String proofString;
    private String css;
    private PositionTable posTable;

    private boolean useRegex = false;

    private TreeMap<Integer, String[]> tagsAtIndex;
    private Range mouseoverRange;
    private ArrayList<Integer> searchIndices;

    private final String closingTag = "</span>";
    private final String mouseTagOpen = "<span class=\"mouseover\">";
    private final String highlightedTagOpen = "<span class=\"highlighted\">";
    
    private enum StylePos{
        SYNTAX(0), MOUSE(1), SEARCH(2);
        private int slotPosition;
        private StylePos(int i){
            slotPosition = i;
        }
    }

    /**
     * 
     */
    public SequentPrinter(String cssPath, PositionTable posTable) {
        try {
            readCSS(cssPath);
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        this.setPosTable(posTable);
        tagsAtIndex = new TreeMap<Integer, String[]>();
    }

    /**
     * prints a Sequent as HTML with styling
     * 
     * @param s
     *            input SequentString from LogicPrinter
     * @return HTML Text with default style
     */
    public String printProofString() {
        int offset = 0;
        StringBuilder sb = new StringBuilder(proofString);

        String insertTag;
        // Iterate over sorted Map
        for (int index : tagsAtIndex.keySet()) {

            // Insert closeTag "<\span>"
            for (int i = 0; i < 3; i++) {
                insertTag = tagsAtIndex.get(index)[i];
                if (insertTag != null && insertTag.equals(closingTag)) {
                    sb.insert(index + offset, closingTag);

                    // Adjust Offset for following insertions
                    offset += closingTag.length();
                }
            }

            // insert openTags "<span class=...>"
            for (int i = 0; i < 3; i++) {
                insertTag = tagsAtIndex.get(index)[i];
                if (insertTag != null && !insertTag.equals(closingTag)) {
                    sb.insert(index + offset, insertTag);

                    // Adjust Offset
                    offset += insertTag.length();
                }

            }
        }
        // Apply HTML formatting and return
        return toHTML(encodeLessThan(sb.toString()));
    }

    /**
     * replaces all "<" signs of the orig. proofString with "&lt;". This avoids
     * HTML Tag misinterpretation. "<" Signs from the HTML tags used for styling
     * are not affected.
     * 
     * @param string
     *            The String in which the < signs shall be replaced
     * @return a cleaned up string.
     */
    private String encodeLessThan(String string) {

        String[] strings = string.split("<");
        StringBuilder stringBuilder = new StringBuilder();

        // Iterate to i < Length-1, as last String[] part has no following "<"
        // sign.
        for (int i = 0; i < strings.length - 1; i++) {
            stringBuilder.append(strings[i]);

            // Append "<" or "&lt;" depending on the beginning of the following
            // String[] part
            if (strings[i + 1].startsWith("span ")
                    || strings[i + 1].startsWith("/span")) {
                stringBuilder.append("<");
            }
            else {
                stringBuilder.append("&lt;");
            }

        }
        // Append last String[]
        stringBuilder.append(strings[strings.length - 1]);

        return stringBuilder.toString();
    }

    /**
     * applies mouseoverHighlighting for the given range
     * 
     * @param range
     *            the Range Object specifying the proofstring part to be
     *            highlighted
     */
    public void applyMouseHighlighting(Range range) {
        removeMouseHighlighting();
        putTag(range.start(), StylePos.MOUSE, mouseTagOpen);
        putTag(range.end(), StylePos.MOUSE, closingTag);
        mouseoverRange = range;
    }

    /**
     * inserts the given Tags at the specified position in the TreeMap. This
     * TreeMap is used to define the stylingTag positions
     * 
     * @param index
     *            index position for the style Tag
     * @param arrayPos
     *            the arrayPosition. Equals Priority: 0=Syntax < 1=Mouseover <
     *            2= searchHighlight. Smaller Number equals Higher Priority
     * @param tag
     *            the HTML tag to be inserted.
     * @return the TreeMap with the new HashMap.
     */
    private TreeMap<Integer, String[]> putTag(int index, StylePos arrayPos,
            String tag) {
        String[] mapValue = tagsAtIndex.get(index);

        if (mapValue != null) {
            mapValue[arrayPos.slotPosition] = tag;
        }
        else {
            tagsAtIndex.put(index, new String[StylePos.values().length]);
            putTag(index, arrayPos, tag);
        }

        return tagsAtIndex;
    }

    /**
     * removes all the Mouseover Highlighting currently applied.
     */
    public void removeMouseHighlighting() {
        // TODO Delete empty Hashmap
        if (mouseoverRange != null) {
            putTag(mouseoverRange.start(), StylePos.MOUSE, null);
            putTag(mouseoverRange.end(), StylePos.MOUSE, null);
        }
    }

    /**
     * set the String used for Freetext Search Highlighting
     * 
     * @param searchString
     *            the freetext searchString
     */
    public void setFreetextSearch(String searchString) {
        // remove old Search Highlighting
        cleanSearchIndices();
        searchIndices = new ArrayList<Integer>();

        if (!searchString.isEmpty()) {
            if (useRegex) {
                // try-catch block for incomplete Regex Patterns
                try {
                    Pattern pattern = Pattern.compile(searchString);
                    Matcher matcher = pattern.matcher(proofString);

                    // Iterate over all findings and add to TreeMap
                    while (matcher.find()) {

                        // Check all occurrences
                        putTag(matcher.start(), StylePos.SEARCH, highlightedTagOpen);
                        putTag(matcher.end(), StylePos.SEARCH, closingTag);

                        searchIndices.add(matcher.start());
                        searchIndices.add(matcher.end());
                    }
                }
                catch (Exception e) {
                    return;
                }

            }
            else {
                // Find indices of all matches. Put in Map. Put in ArrayList for
                // removal
                for (int i = -1; (i = proofString.indexOf(searchString,
                        i + 1)) != -1;) {
                    putTag(i, StylePos.SEARCH, highlightedTagOpen);
                    putTag(i + searchString.length(), StylePos.SEARCH, closingTag);

                    searchIndices.add(i);
                    searchIndices.add(i + searchString.length());
                }
            }
        }
    }

    /**
     * iterates over the searchIndices ArrayList. Uses this information to
     * remove references in Styling TreeMap
     */
    private void cleanSearchIndices() {
        if (searchIndices != null) {
            for (Iterator<Integer> iterator = searchIndices.iterator(); iterator
                    .hasNext();) {
                int index = (int) iterator.next();
                putTag(index, StylePos.SEARCH, null);
            }
        }
    }

    /**
     * @param proofString
     *            the proofString to set
     */
    public void setProofString(String proofString) {
        this.proofString = proofString;

        // As a new ProofString means old styling Info is deprecated, Map is
        // cleared.
        tagsAtIndex.clear();
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
            StringBuilder sb = new StringBuilder();
            String line = br.readLine();

            while (line != null) {
                sb.append(line);
                sb.append("\n");
                line = br.readLine();
            }
            this.css = sb.toString();
        }
        finally {
            br.close();
        }
    }

    /**
     * @param posTable
     *            the posTable to set
     */
    public void setPosTable(PositionTable posTable) {
        this.posTable = posTable;
    }

    /**
     * converts the input String to HTML tagged text
     * 
     * @param s
     *            input string
     * @return String with HTML tags
     */
    private String toHTML(String s) {
        StringBuilder sb = new StringBuilder();
        sb.append("<style>");
        sb.append(css);
        sb.append("</style>");
        sb.append("<pre class=\"content\">");

        sb.append(s);

        sb.append("</pre>");

        return sb.toString();
    }

    /**
     * sets useRegex
     * 
     * @param b
     *            new boolean Value
     */
    public void setUseRegex(boolean b) {
        useRegex = b;

    }
}
