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

import de.uka.ilkd.key.nui.model.PrintFilter;
import de.uka.ilkd.key.nui.view.DebugViewController;
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
    private ArrayList<Integer> filterIndices;

    private final static String closingTag = "</span>";

    private final static String mouseTagOpen = "<span class=\"mouseover\">";
    private final static String highlightedTagOpen = "<span class=\"highlighted\">";
    private final static String filterMinimizeTagOpen = "<span class=\"minimized\">";
    private final static String filterCollapsedTagOpen = "<span class=\"collapsed\">";

    private enum StylePos {
        SYNTAX(0), MOUSE(1), SEARCH(2), FILTER(3);

        private int slotPosition;

        private StylePos(int i) {
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
        searchIndices = new ArrayList<Integer>();
        filterIndices = new ArrayList<Integer>();
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
            for (int i = 0; i < StylePos.values().length; i++) {
                insertTag = tagsAtIndex.get(index)[i];
                if (insertTag != null && insertTag.equals(closingTag)) {
                    sb.insert(index + offset, closingTag);

                    // Adjust Offset for following insertions
                    offset += closingTag.length();
                }
            }

            // insert openTags "<span class=...>"
            for (int i = 0; i < StylePos.values().length; i++) {
                insertTag = tagsAtIndex.get(index)[i];
                if (insertTag != null && !insertTag.equals(closingTag)) {
                    sb.insert(index + offset, insertTag);

                    // Adjust Offset
                    offset += insertTag.length();
                }

            }
        }

        // Apply HTML formatting and return
        DebugViewController.PrintOnCurrent(encodeLessThan(sb.toString()));
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
     * styles the text according to given Filter
     * 
     * @param filter
     */
    public void applyFilter(PrintFilter filter) {
        ArrayList<Integer> indicesOfLines = SequentFilterer
                .ApplyFilter(proofString, filter);

        // remove old Filter styling
        removeFilter();

        if (!indicesOfLines.isEmpty()) {
            // Sort Lines
            // Collections.sort(indicesOfLines);
            // get line information
            String[] lines = proofString.split("\n");

            int styleStart = 0;
            // Pointer at the current entry of the ArrayList
            int linePointer = 0;

            // Iterate over the lines
            for (int i = 0; i < lines.length; i++) {
                // Compute Endindex of Line
                int styleEnd = styleStart + lines[i].length()+1;
                // If line is in list apply styles
                if (indicesOfLines.contains(i) == filter.getInvert()) {

                    switch (filter.getFilterMode()) {
                    case Minimize:
                        minimizeLine(styleStart, styleEnd);
                        break;
                    case Collapse:
                    default:
                        collapseLine(styleStart, styleEnd);
                        break;
                    }
                    // Increase Linepointer for the ArrayList entry
                    linePointer++;
                }
                // If all the entries have been resolved, return
//                if (linePointer == indicesOfLines.size()) {
//                    break;
//                }
                // Set the start of the next line to the end of the current
                // line. Adjust +1 for \n char
                styleStart = styleEnd;
            }
        }
    }

    /**
     * adds collapsed Style for the line defined by the indices
     * 
     * @param lineStart
     *            startIndex of line
     * @param lineEnd
     *            endIndex of line
     */
    private void collapseLine(int lineStart, int lineEnd) {
        putTag(lineStart, StylePos.FILTER, filterCollapsedTagOpen);
        putTag(lineEnd, StylePos.FILTER, closingTag);

        filterIndices.add(lineStart);
        filterIndices.add(lineEnd);
    }

    /**
     * adds minimized Style for the line defined by the indices
     * 
     * @param lineStart
     *            startIndex of line
     * @param lineEnd
     *            endIndex of line
     */
    private void minimizeLine(int lineStart, int lineEnd) {
        putTag(lineStart, StylePos.FILTER, filterMinimizeTagOpen);
        putTag(lineEnd, StylePos.FILTER, closingTag);

        filterIndices.add(lineStart);
        filterIndices.add(lineEnd);
    }

    /**
     * removes all the applied Styling by the filter functions
     */
    private void removeFilter() {
        if (filterIndices != null) {
            for (Iterator<Integer> iterator = filterIndices.iterator(); iterator
                    .hasNext();) {
                int index = (int) iterator.next();
                putTag(index, StylePos.FILTER, "");
            }
            filterIndices.clear();
        }
    }

    /**
     * inserts the given Tags at the specified position in the TreeMap. This
     * TreeMap is used to define the stylingTag positions
     * 
     * @param index
     *            index position for the style Tag
     * @param arrayPos
     *            the arrayPosition. Should correspond to a priority value.
     * @param tag
     *            the HTML tag to be inserted.
     * @return the TreeMap with the new HashMap.
     */
    private TreeMap<Integer, String[]> putTag(int index, StylePos arrayPos,
            String tag) {
        String[] mapValue = tagsAtIndex.get(index);
        // If Map Entry already exists
        if (mapValue != null) {
            // If Array entry is null or shall be cleared (filled with empty
            // String), fill the array
            if (mapValue[arrayPos.slotPosition] == null || tag.isEmpty()) {
                mapValue[arrayPos.slotPosition] = tag;
            }
            else {
                // If the Array entry is not null, the tag can be appended.
                // Solves the problem with double consecutive chars
                // ("wellformed")
                mapValue[arrayPos.slotPosition] += tag;
            }
        }
        else {
            // If the Map Entry does not exist, create new Entry and call itself
            // again. RECURSION!
            tagsAtIndex.put(index, new String[StylePos.values().length]);
            putTag(index, arrayPos, tag);
        }

        return tagsAtIndex;
    }

    /**
     * removes all the Mouseover Highlighting currently applied.
     */
    public void removeMouseHighlighting() {
        if (mouseoverRange != null) {
            putTag(mouseoverRange.start(), StylePos.MOUSE, "");
            putTag(mouseoverRange.end(), StylePos.MOUSE, "");
        }
    }

    /**
     * set the String used for Freetext Search Highlighting
     * 
     * @param searchString
     *            the freetext searchString
     */
    public void applyFreetextSearch(String searchString) {
        // remove old Search Highlighting
        removeSearchIndices();

        if (!searchString.isEmpty()) {
            if (useRegex) {
                // try-catch block for incomplete Regex Patterns
                try {
                    Pattern pattern = Pattern.compile(searchString);
                    Matcher matcher = pattern.matcher(proofString);

                    // Iterate over all findings and add to TreeMap
                    while (matcher.find()) {

                        // Check all occurrences
                        putTag(matcher.start(), StylePos.SEARCH,
                                highlightedTagOpen);
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
                    putTag(i + searchString.length(), StylePos.SEARCH,
                            closingTag);

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
    private void removeSearchIndices() {
        if (searchIndices != null) {
            for (Iterator<Integer> iterator = searchIndices.iterator(); iterator
                    .hasNext();) {
                int index = (int) iterator.next();
                putTag(index, StylePos.SEARCH, "");
            }
            searchIndices.clear();
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

        /*
         * Stub for SyntaxHighlight applySyntaxHighlighting();
         */
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

    // private void applySyntaxHighlighting() {
    // InitialPositionTable initPos = (InitialPositionTable) posTable;
    // IdentitySequentPrintFilter filter = new IdentitySequentPrintFilter(p_s);
    // for (int i = 0; i < proofString.length(); i++) {
    // System.out.println(
    // initPos.getPosInSequent(i, filter).getPosInOccurrence()
    // .constrainedFormula().getClass().getName());
    // }
    // }

    /**
     * converts the input String to HTML tagged text
     * 
     * @param s
     *            input string
     * @return String with HTML tags
     */
    private String toHTML(String s) {
        StringBuilder sb = new StringBuilder();
        sb.append("<head>");
        sb.append("<style>");
        sb.append(css);
        sb.append("</style>");
        sb.append("</head><body>");
        sb.append("<pre class=\"content\">");

        sb.append(s);

        sb.append("</pre></body>");

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
