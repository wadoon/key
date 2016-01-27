/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.nui.model.PrintFilter;
import de.uka.ilkd.key.nui.view.DebugViewController;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.PosInSequent;
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
    private Sequent sequent;
    private boolean useRegex = false;

    private TreeMap<Integer, String[]> openTagsAtIndex;
    private TreeMap<Integer, String[]> closeTagsAtIndex;

    private Range mouseoverRange;
    private ArrayList<Integer> searchIndices;
    private ArrayList<Integer> filterIndices;

    private static HashMap<Class, String> classMap = new HashMap<>();

    private final static String closingTag = "</span>";

    private final static String mouseTagOpen = "<span class=\"mouseover\">";
    private final static String highlightedTagOpen = "<span class=\"highlighted\">";
    private final static String filterMinimizeTagOpen = "<span class=\"minimized\">";
    private final static String filterCollapsedTagOpen = "<span class=\"collapsed\">";

    private enum StylePos {
        SYNTAX(3), MOUSE(0), SEARCH(1), FILTER(2);

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

        openTagsAtIndex = new TreeMap<Integer, String[]>();
        searchIndices = new ArrayList<Integer>();
        filterIndices = new ArrayList<Integer>();

        // If no SequentPrinter has been created yet, the ClassMap is empty.
        // Fill it!
        if (classMap.size() == 0) {
            fillClassMap();
        }

    }

    /**
     * fills the classMap with each class name and its styleClass tag
     */
    private static void fillClassMap() {
        classMap.put(de.uka.ilkd.key.logic.op.Equality.class,
                "<span class=\"equality\">");
        classMap.put(de.uka.ilkd.key.logic.op.Function.class,
                "<span class=\"function\">");
        classMap.put(de.uka.ilkd.key.logic.op.LocationVariable.class,
                "<span class=\"locationVar\">");
        classMap.put(de.uka.ilkd.key.logic.op.Junctor.class,
                "<span class=\"junctor\">");
        classMap.put(de.uka.ilkd.key.logic.op.LogicVariable.class,
                "<span class=\"logicVar\">");
        classMap.put(de.uka.ilkd.key.logic.op.Quantifier.class,
                "<span class=\"quantifier\">");
        classMap.put(de.uka.ilkd.key.logic.op.SortDependingFunction.class,
                "<span class=\"sortDepFunc\">");
        classMap.put(de.uka.ilkd.key.logic.op.Modality.class,
                "<span class=\"modality\">");
        classMap.put(de.uka.ilkd.key.logic.op.ObserverFunction.class,
                "<span class=\"observerFunc\">");
        classMap.put(de.uka.ilkd.key.logic.op.AbstractSortedOperator.class,
                "<span class=\"abstractSortOp\">");
        classMap.put(de.uka.ilkd.key.logic.op.AbstractSV.class,
                "<span class=\"abstractSV\">");
        classMap.put(de.uka.ilkd.key.logic.op.AbstractTermTransformer.class,
                "<span class=\"abstractTermTransf\">");
        classMap.put(de.uka.ilkd.key.logic.op.ElementaryUpdate.class,
                "<span class=\"elemUpdate\">");
        classMap.put(de.uka.ilkd.key.logic.op.FormulaSV.class,
                "<span class=\"formulaSV\">");
        classMap.put(de.uka.ilkd.key.logic.op.IfExThenElse.class,
                "<span class=\"ifExThenElse\">");
        classMap.put(de.uka.ilkd.key.logic.op.IfThenElse.class,
                "<span class=\"ifThenElse\">");
        classMap.put(de.uka.ilkd.key.logic.op.ModalOperatorSV.class,
                "<span class=\"modalOpSV\">");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramConstant.class,
                "<span class=\"progConst\">");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramMethod.class,
                "<span class=\"progMeth\">");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramSV.class,
                "<span class=\"progSV\">");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramVariable.class,
                "<span class=\"progVar\">");
        classMap.put(de.uka.ilkd.key.logic.op.SchemaVariableFactory.class,
                "<span class=\"schemaVarFactory\">");
        classMap.put(de.uka.ilkd.key.logic.op.SkolemTermSV.class,
                "<span class=\"skolemTermSV\">");
        classMap.put(de.uka.ilkd.key.logic.op.SubstOp.class,
                "<span class=\"substOp\">");
        classMap.put(de.uka.ilkd.key.logic.op.TermLabelSV.class,
                "<span class=\"termLabelSV\">");
        classMap.put(de.uka.ilkd.key.logic.op.TermSV.class,
                "<span class=\"termSV\">");
        classMap.put(de.uka.ilkd.key.logic.op.Transformer.class,
                "<span class=\"transformer\">");
        classMap.put(de.uka.ilkd.key.logic.op.UpdateApplication.class,
                "<span class=\"updateApp\">");
        classMap.put(de.uka.ilkd.key.logic.op.UpdateJunctor.class,
                "<span class=\"updateJunc\">");
        classMap.put(de.uka.ilkd.key.logic.op.UpdateSV.class,
                "<span class=\"updateSV\">");
        classMap.put(de.uka.ilkd.key.logic.op.VariableSV.class,
                "<span class=\"varSV\">");
        classMap.put(de.uka.ilkd.key.logic.op.WarySubstOp.class,
                "<span class=\"warySubstOp\">");
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
        for (int index : openTagsAtIndex.keySet()) {

            // Insert closeTag "<\span>"
            for (int i = 0; i < StylePos.values().length; i++) {
                insertTag = openTagsAtIndex.get(index)[i];
                if (insertTag != null && insertTag.equals(closingTag)) {
                    sb.insert(index + offset, closingTag);

                    // Adjust Offset for following insertions
                    offset += closingTag.length();
                }
            }

            // insert openTags "<span class=...>"
            for (int i = 0; i < StylePos.values().length; i++) {
                insertTag = openTagsAtIndex.get(index)[i];
                if (insertTag != null && !insertTag.equals(closingTag)) {
                    sb.insert(index + offset, insertTag);

                    // Adjust Offset
                    offset += insertTag.length();
                }

            }
        }

        // Apply HTML formatting and return
        DebugViewController.printOnCurrent(encodeLessThan(sb.toString()));
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
                .applyFilter(proofString, filter);

        // remove old Filter styling
        removeFilter();

        if (!indicesOfLines.isEmpty()) {
            // get line information
            String[] lines = proofString.split("\n");

            int styleStart = 0;
            // Pointer at the current entry of the ArrayList

            // Iterate over the lines
            for (int i = 0; i < lines.length; i++) {
                // Compute Endindex of Line
                int styleEnd = styleStart + lines[i].length() + 1;
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

                }

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
        String[] mapValue = openTagsAtIndex.get(index);
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
            openTagsAtIndex.put(index, new String[StylePos.values().length]);
            putTag(index, arrayPos, tag);
        }

        return openTagsAtIndex;
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
                catch (RuntimeException e) {
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
        openTagsAtIndex.clear();

        applySyntaxHighlighting();

    }

    /**
     * reads the CSS information for HTML Styling
     * 
     * @param fileName
     *            path to the CSS file
     * @throws IOException
     */
    private void readCSS(String fileName) throws IOException {
        BufferedReader br = new BufferedReader(
                new InputStreamReader(new FileInputStream(fileName), "UTF-8"));
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
     * puts Syntax Styling Info in tagsAtIndex Map
     */
    private void applySyntaxHighlighting() {

        InitialPositionTable initPos = (InitialPositionTable) posTable;
        IdentitySequentPrintFilter filter = new IdentitySequentPrintFilter(
                sequent);

        Class lastClass = null;
        int lastIndex = 0;
        boolean openedTag = false;

        // Iterate over String. Insert Tags according to class.
        for (int i = 0; i < proofString.length(); i++) {
            PosInSequent pos = initPos.getPosInSequent(i, filter);

            System.out.println(i + " "+ proofString.charAt(i));

            // Close Tag on Whitespace, if it was opened before
            if (openedTag && (proofString.charAt(i) == ' '
                    || proofString.charAt(i) == '\n')) {

                System.out.println("CLOSE WHITESPACE");

                putTag(i, StylePos.SYNTAX, closingTag);
                openedTag = false;
                lastClass = null;
            }
            // Check if there is a Class in AST for this pos
            else if (pos != null) {
                PosInOccurrence oc = pos.getPosInOccurrence();
                if (oc != null && oc.posInTerm() != null) {
                    Operator op = oc.subTerm().op();

                    // Open First Tag
                    if (lastClass == null
                            && classMap.containsKey(op.getClass())) {

                        System.out.println("OPEN NEW TAG");

                        putTag(i, StylePos.SYNTAX, classMap.get(op.getClass()));
                        openedTag = true;
                        lastClass = op.getClass();
                    }

                    // If Class changed, close the existing Tag, open new one
                    else if (lastClass != null && lastClass != op.getClass()) {

                        System.out.println("CLOSE TAG");

                        putTag(i, StylePos.SYNTAX, closingTag);
                        openedTag = false;
                        if (classMap.containsKey(op.getClass())) {

                            System.out.println("OPEN NEW AFTER CLOSE");

                            putTag(i, StylePos.SYNTAX,
                                    classMap.get(op.getClass()));
                            openedTag = true;
                        }
                        // Syso to let the user know the AST Class is unknown
                        else {
                            System.out.println("");
                            System.out.println(
                                    "The following Class does not exist in the ClassDictionary");
                            System.out.println("EXPRESSION: " + op);
                            System.out.println("CLASS: " + op.getClass());
                            System.out.println("");
                        }
                        lastClass = op.getClass();
                    }
                    lastIndex = i;
                }
            }
            // else {
            // // putTag(i, StylePos.SYNTAX, closingTag);
            // lastClass = null;
            // }

        }

        System.out.println("CLOSE LAST TAG");
        System.out.println("##################");
        putTag(lastIndex, StylePos.SYNTAX, closingTag);

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

    public void setSequent(Sequent sequent) {
        this.sequent = sequent;
    }
}
