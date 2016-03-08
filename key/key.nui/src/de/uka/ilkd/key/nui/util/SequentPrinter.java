/**
 * 
 */
package de.uka.ilkd.key.nui.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Stack;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.swing.text.BadLocationException;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.nui.Context;
import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.PositionTable;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Pair;

/**
 * @author Maximilian Li
 * @author Victor Schuemmer
 *
 */
public class SequentPrinter {
    private String proofString;
    private CssFileHandler cssFileHandler;
    private PositionTable posTable;
    private Sequent sequent;
    private boolean useRegex = false;

    private TreeSet<Integer> keySet = new TreeSet<Integer>();

    // HashMap maps Index in ProofString to Styling Info Array
    // Array holds Styling Info separated for every Styling Case.
    // Array Slots Defined in StylePos Enum
    // ArrayList inside of Array: List of all Tags
    private HashMap<Integer, ArrayList<String>[]> openTagsAtIndex = new HashMap<Integer, ArrayList<String>[]>();;
    private HashMap<Integer, ArrayList<String>[]> closeTagsAtIndex = new HashMap<Integer, ArrayList<String>[]>();;

    private ArrayList<Integer> lessThenList = new ArrayList<Integer>();

    private Range mouseRange;
    private ArrayList<Integer> searchIndicesOpen = new ArrayList<Integer>();
    private ArrayList<Integer> searchIndicesClose = new ArrayList<Integer>();
    private ArrayList<Integer> filterIndicesOpen = new ArrayList<Integer>();
    private ArrayList<Integer> filterIndicesClose = new ArrayList<Integer>();
    private ArrayList<Integer> filterCollapseIndicator = new ArrayList<Integer>();

    // Use Unique values in incremental order. Value Correspond to
    // ArrayPosition. Higher Value = Higher Priority.
    private enum StylePos {
        MOUSE(0), FILTER(1), SELECTION(2), RULEAPP(3), SEARCH(4), SYNTAX(5);

        private int slotPosition;

        private StylePos(int i) {
            slotPosition = i;
        }
    }

    private Context context;

    /**
     * 
     */
    public SequentPrinter(CssFileHandler cssFileHandler, PositionTable posTable,
            Context context) {
        this.cssFileHandler = cssFileHandler;
        this.setPosTable(posTable);

        this.context = context;

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
        Stack<Pair<Integer, String>> tagStack = new Stack<>();
        Stack<Pair<Integer, String>> saveTagStack = new Stack<>();

        ArrayList<String> insertTagList;

        for (Integer i : keySet) {
            // Apply Close Tags first
            if (closeTagsAtIndex.containsKey(i)) {
                for (int j = StylePos.values().length - 1; j >= 0; j--) {
                    insertTagList = closeTagsAtIndex.get(i)[j];
                    if (insertTagList == null)
                        continue;
                    for (String insertTag : insertTagList) {
                        if (insertTag == null || insertTag.isEmpty())
                            continue;

                        // Check for possible Overlap
                        while (!tagStack.isEmpty()
                                && tagStack.peek().first != j) {
                            sb.insert(i + offset, NUIConstants.CLOSING_TAG);
                            offset += NUIConstants.CLOSING_TAG.length();
                            saveTagStack.push(tagStack.pop());
                        }

                        sb.insert(i + offset, insertTag);
                        offset += insertTag.length();
                        tagStack.pop();

                        while (saveTagStack.size() > 0) {
                            sb.insert(i + offset, saveTagStack.peek().second);
                            offset += saveTagStack.peek().second.length();
                            tagStack.push(saveTagStack.pop());
                        }
                    }
                }
            }
            // Apply OpenTags
            if (openTagsAtIndex.containsKey(i)) {
                for (int j = 0; j < StylePos.values().length; j++) {
                    insertTagList = openTagsAtIndex.get(i)[j];
                    if (insertTagList == null)
                        continue;
                    for (String insertTag : insertTagList) {
                        if (insertTag == null || insertTag.isEmpty())
                            continue;

                        // Correctly Prioritze even inside other spans
                        while (!tagStack.isEmpty()
                                && tagStack.peek().first > j) {
                            sb.insert(i + offset, NUIConstants.CLOSING_TAG);
                            offset += NUIConstants.CLOSING_TAG.length();
                            saveTagStack.push(tagStack.pop());
                        }

                        tagStack.push(new Pair<Integer, String>(j, insertTag));

                        sb.insert(i + offset, insertTag);
                        offset += insertTag.length();

                        while (saveTagStack.size() > 0) {
                            sb.insert(i + offset, saveTagStack.peek().second);
                            offset += saveTagStack.peek().second.length();
                            tagStack.push(saveTagStack.pop());
                        }

                    }
                }
            }
            if (filterCollapseIndicator.contains(i)) {
                sb.insert(i + offset, "...\n");
                offset += 4;
            }
            // HTML Formatting
            if (lessThenList.contains(i)) {
                sb.replace(i + offset, i + offset + 1, "&lt;");
                offset += 3;
            }

            // Clean KeySet
            if (!closeTagsAtIndex.containsKey(i)
                    && !openTagsAtIndex.containsKey(i)
                    && !lessThenList.contains(i)) {
                keySet.remove(i);
            }
        }

        String html = sb.toString();
        context.setSequentHtml(html);
        return

        toHTML(html);
    }

    private Range getHighlightRange(PosInOccurrence pos) {
        if (!(posTable instanceof InitialPositionTable)) {
            throw new AssertionError(
                    "Unexpected type (should be InitialPositionTable: "
                            + posTable);
        }
        ImmutableList<Integer> path = ((InitialPositionTable) posTable)
                .pathForPosition(pos, new IdentitySequentPrintFilter(sequent));
        return ((InitialPositionTable) posTable).rangeForPath(path);
    }

    public void applyRuleAppHighlighting(RuleApp app) {
        if (app.posInOccurrence() != null) {
            Range r = getHighlightRange(app.posInOccurrence());
            putOpenTag(r.start(), StylePos.RULEAPP, NUIConstants.RULE_APP_TAG);
            putCloseTag(r.end(), StylePos.RULEAPP, NUIConstants.CLOSING_TAG);
            keySet.add(r.start());
            keySet.add(r.end());
        }

        if (app instanceof TacletApp) {
            highlightIfFormulas((TacletApp) app);
        }
        else if (app instanceof IBuiltInRuleApp) {
            highlightIfInsts((IBuiltInRuleApp) app);
        }
    }

    /**
     * @param tapp
     *            The taclet app for which the if formulae should be
     *            highlighted.
     * @throws BadLocationException
     */
    private void highlightIfFormulas(TacletApp tapp) {
        final ImmutableList<IfFormulaInstantiation> ifs = tapp
                .ifFormulaInstantiations();
        if (ifs == null) {
            return;
        }
        for (final IfFormulaInstantiation inst2 : ifs) {
            if (!(inst2 instanceof IfFormulaInstSeq)) {
                continue;
            }
            final IfFormulaInstSeq inst = (IfFormulaInstSeq) inst2;
            final PosInOccurrence pos = new PosInOccurrence(
                    inst.getConstrainedFormula(), PosInTerm.getTopLevel(),
                    inst.inAntec());
            Range r = getHighlightRange(pos);
            putOpenTag(r.start(), StylePos.RULEAPP,
                    NUIConstants.IF_FORMULA_TAG);
            putCloseTag(r.end(), StylePos.RULEAPP, NUIConstants.CLOSING_TAG);
            keySet.add(r.start());
            keySet.add(r.end());
        }
    }

    private void highlightIfInsts(IBuiltInRuleApp bapp) {
        final ImmutableList<PosInOccurrence> ifs = bapp.ifInsts();
        for (PosInOccurrence pio : ifs) {
            Range r = getHighlightRange(pio);
            putOpenTag(r.start(), StylePos.RULEAPP, NUIConstants.IF_INST_TAG);
            putCloseTag(r.end(), StylePos.RULEAPP, NUIConstants.CLOSING_TAG);
            keySet.add(r.start());
            keySet.add(r.end());
        }
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

        keySet.add(range.start());
        keySet.add(range.end());

        putOpenTag(range.start(), StylePos.MOUSE, NUIConstants.MOUSE_TAG);
        putCloseTag(range.end(), StylePos.MOUSE, NUIConstants.CLOSING_TAG);

        mouseRange = range;
    }

    /**
     * styles the text according to given Filter
     * 
     * @param filter
     */
    public void applyFilter(ArrayList<Integer> indicesOfLines,
            FilterLayout layout) {
        // remove old Filter styling
        removeFilter();
        // get line information
        String[] lines = proofString.split("\n");

        int styleStart = 0;
        // Pointer at the current entry of the ArrayList

        // Iterate over the lines
        for (int i = 0; i < lines.length; i++) {
            // Compute Endindex of Line
            int styleEnd = styleStart + lines[i].length() + 1;

            // If line is in list apply styles
            if (!indicesOfLines.contains(i)) {
                switch (layout) {
                case Minimize:
                    minimizeLine(styleStart, styleEnd);
                    break;
                case Collapse:
                    // Add collapsed indicator if collapsed Block ends, or the
                    // last line is reached
                    if (indicesOfLines.contains(i + 1)
                            || i == lines.length - 1) {
                        filterCollapseIndicator.add(styleEnd);
                    }
                default:
                    collapseLine(styleStart, styleEnd);
                    break;
                }
            }
            styleStart = styleEnd;
        }
        keySet.addAll(filterIndicesOpen);
        keySet.addAll(filterIndicesClose);
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
        putOpenTag(lineStart, StylePos.FILTER,
                NUIConstants.FILTER_COLLAPSED_TAG);
        putCloseTag(lineEnd, StylePos.FILTER, NUIConstants.CLOSING_TAG);

        filterIndicesOpen.add(lineStart);
        filterIndicesClose.add(lineEnd);
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
        putOpenTag(lineStart, StylePos.FILTER,
                NUIConstants.FILTER_MINIMIZED_TAG);
        putCloseTag(lineEnd, StylePos.FILTER, NUIConstants.CLOSING_TAG);

        filterIndicesOpen.add(lineStart);
        filterIndicesClose.add(lineEnd);
    }

    /**
     * removes all the applied Styling by the filter functions
     */
    private void removeFilter() {
        if (filterIndicesOpen != null) {
            for (Iterator<Integer> iterator = filterIndicesOpen
                    .iterator(); iterator.hasNext();) {
                int index = (int) iterator.next();
                putOpenTag(index, StylePos.FILTER, "");
            }
            for (Iterator<Integer> iterator = filterIndicesClose
                    .iterator(); iterator.hasNext();) {
                int index = (int) iterator.next();
                putCloseTag(index, StylePos.FILTER, "");
            }

            filterIndicesOpen.clear();
            filterIndicesClose.clear();
            filterCollapseIndicator.clear();
        }
    }

    /**
     * inserts the tag into the given HashMap. Use only if you are sure you know
     * what to do
     * 
     * @param index
     *            position inside the proofstring
     * @param arrayPos
     *            the StylePosition
     * @param tag
     *            the tag itself.
     * @param map
     *            the map to be inserted into
     */
    private void putTag(int index, StylePos arrayPos, String tag,
            HashMap<Integer, ArrayList<String>[]> map) {
        ArrayList<String>[] mapValue = map.get(index);
        // If Map Entry already exists
        if (mapValue != null) {
            // ArrayList<String> tagList = mapValue[arrayPos.slotPosition];
            // If Array entry is null make ArrayList and add tag
            if (mapValue[arrayPos.slotPosition] == null) {
                mapValue[arrayPos.slotPosition] = new ArrayList<>();
                mapValue[arrayPos.slotPosition].add(tag);
            }
            else {
                // If Tag is empty, one entry shall be removed
                if (tag.isEmpty()) {
                    mapValue[arrayPos.slotPosition]
                            .remove(mapValue[arrayPos.slotPosition].size() - 1);
                }
                else {
                    // If the Array entry is not null, the tag can be appended.
                    // Solves the problem with double consecutive chars
                    // ("wellformed")
                    mapValue[arrayPos.slotPosition].add(tag);
                }

            }
        }
        else {
            // If the Map Entry does not exist, create new Entry and call itself
            // again. RECURSION!
            map.put(index, new ArrayList[StylePos.values().length]);
            putTag(index, arrayPos, tag, map);
        }
    }

    /**
     * to be used to add an opening <span...> tag. Calls {@link putTag}
     * 
     * @param index
     *            position inside the proofstring
     * @param arrayPos
     *            the StylePosition
     * @param tag
     *            the opening tag const or empty String
     * @return the HashMap with all the openTag indices
     */
    private HashMap<Integer, ArrayList<String>[]> putOpenTag(int index,
            StylePos arrayPos, String tag) {
        if (tag.isEmpty()) {
            putTag(index, arrayPos, tag, openTagsAtIndex);
        }
        else {
            putTag(index, arrayPos, NUIConstants.OPEN_TAG_BEGIN.concat(tag)
                    .concat(NUIConstants.OPEN_TAG_END), openTagsAtIndex);
        }

        return openTagsAtIndex;
    }

    /**
     * to be used to add a closing </span> tag. Calls {@link putTag}
     * 
     * @param index
     *            position inside the proofstring
     * @param arrayPos
     *            the StylePosition
     * @param tag
     *            the closingTag const or empty String
     * @return the HashMap with all the closeTag indices
     */
    private HashMap<Integer, ArrayList<String>[]> putCloseTag(int index,
            StylePos arrayPos, String tag) {
        putTag(index, arrayPos, tag, closeTagsAtIndex);
        return closeTagsAtIndex;
    }

    /**
     * removes all the Mouseover Highlighting currently applied.
     */
    public void removeMouseHighlighting() {
        if (mouseRange != null) {
            putOpenTag(mouseRange.start(), StylePos.MOUSE, "");
            putCloseTag(mouseRange.end(), StylePos.MOUSE, "");
            mouseRange = null;
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
                        putOpenTag(matcher.start(), StylePos.SEARCH,
                                NUIConstants.HIGHLIGHTED_TAG);
                        putCloseTag(matcher.end(), StylePos.SEARCH,
                                NUIConstants.CLOSING_TAG);

                        searchIndicesOpen.add(matcher.start());
                        searchIndicesClose.add(matcher.end());
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
                    putOpenTag(i, StylePos.SEARCH,
                            NUIConstants.HIGHLIGHTED_TAG);
                    putCloseTag(i + searchString.length(), StylePos.SEARCH,
                            NUIConstants.CLOSING_TAG);

                    searchIndicesOpen.add(i);
                    searchIndicesClose.add(i + searchString.length());
                }
            }
        }

        keySet.addAll(searchIndicesOpen);
        keySet.addAll(searchIndicesClose);
    }

    /**
     * iterates over the searchIndices ArrayList. Uses this information to
     * remove references in Styling TreeMap
     */
    private void removeSearchIndices() {
        if (searchIndicesOpen != null) {
            for (Iterator<Integer> iterator = searchIndicesOpen
                    .iterator(); iterator.hasNext();) {
                int index = (int) iterator.next();
                putOpenTag(index, StylePos.SEARCH, "");
            }
            for (Iterator<Integer> iterator = searchIndicesClose
                    .iterator(); iterator.hasNext();) {
                int index = (int) iterator.next();
                putCloseTag(index, StylePos.SEARCH, "");
            }

            // keySet.removeAll(filterIndicesOpen);
            // keySet.removeAll(filterIndicesClose);

            searchIndicesOpen.clear();
            searchIndicesClose.clear();

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
        lessThenList.clear();
        openTagsAtIndex.clear();
        closeTagsAtIndex.clear();
        keySet.clear();

        setLessThenIndices(proofString);
        applySyntaxHighlighting();

    }

    /**
     * adds the Indices of all the "<" signs inside the given String for
     * Escaping
     * 
     * @param string
     *            the string to be escaped
     */
    private void setLessThenIndices(String string) {
        // Find indices of all matches. Put in Map. Put in ArrayList for
        // removal
        for (int i = -1; (i = proofString.indexOf("<", i + 1)) != -1;) {
            lessThenList.add(i);
            keySet.add(i);
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

        if (!(posTable instanceof InitialPositionTable)) {
            throw new AssertionError(
                    "Unexpected type (should be InitialPositionTable: "
                            + posTable);
        }
        InitialPositionTable initPos = (InitialPositionTable) posTable;

        IdentitySequentPrintFilter filter = new IdentitySequentPrintFilter(
                sequent);

        // TODO References to generic type Class<T> should be parameterized
        Class lastClass = null;
        boolean openedTag = false;

        // Iterate over String. Insert Tags according to class.
        for (int i = 0; i < proofString.length(); i++) {
            PosInSequent pos = initPos.getPosInSequent(i, filter);

            // Close Tag on Whitespace, if it was opened before
            if ((proofString.charAt(i) == ' '
                    || proofString.charAt(i) == '\n')) {
                if (openedTag) {
                    putCloseTag(i, StylePos.SYNTAX, NUIConstants.CLOSING_TAG);
                    keySet.add(i);

                    openedTag = false;
                    lastClass = null;
                }
                else
                    continue;
            }
            // Check if there is a Class in AST for this pos
            else if (pos != null) {
                PosInOccurrence oc = pos.getPosInOccurrence();
                if (oc != null && oc.posInTerm() != null) {
                    Operator op = oc.subTerm().op();

                    // Open First Tag
                    if (lastClass == null
                            && NUIConstants.getClassCssMap()
                                    .containsKey(op.getClass())
                            && NUIConstants.getClassEnabledMap()
                                    .get(op.getClass())) {

                        putOpenTag(i, StylePos.SYNTAX, NUIConstants
                                .getClassCssMap().get(op.getClass()));
                        keySet.add(i);

                        openedTag = true;
                        lastClass = op.getClass();
                    }

                    // If Class changed, close the existing Tag, open new one
                    else if (lastClass != null && lastClass != op.getClass()) {

                        putCloseTag(i, StylePos.SYNTAX,
                                NUIConstants.CLOSING_TAG);
                        keySet.add(i);

                        openedTag = false;
                        if (NUIConstants.getClassCssMap()
                                .containsKey(op.getClass())
                                && NUIConstants.getClassEnabledMap()
                                        .get(op.getClass())) {

                            putOpenTag(i, StylePos.SYNTAX, NUIConstants
                                    .getClassCssMap().get(op.getClass()));
                            keySet.add(i);
                            lastClass = op.getClass();
                            openedTag = true;
                        }
                        // Syso to let the user know the AST Class is unknown
                        else {
                            lastClass = null;
                            openedTag = false;
                            if (!NUIConstants.getClassCssMap()
                                    .containsKey(op.getClass())) {
                                System.out.println("");
                                System.out.println(
                                        "The following Class does not exist in the ClassDictionary");
                                System.out.println("EXPRESSION: " + op);
                                System.out.println("CLASS: " + op.getClass());
                                System.out.println("");
                            }
                        }
                    }

                }
            }
        }
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
        sb.append(cssFileHandler.getCss());
        sb.append("</style>");
        sb.append("</head><body>");
        sb.append("<pre>");

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

    public void applySelection(Range range) {
        keySet.add(range.start());
        keySet.add(range.end());

        putOpenTag(range.start(), StylePos.SELECTION,
                NUIConstants.FILTER_SELECTION_TAG);
        putCloseTag(range.end(), StylePos.SELECTION, NUIConstants.CLOSING_TAG);
    }

    public void removeSelection(Range range) {
        putOpenTag(range.start(), StylePos.SELECTION, "");
        putCloseTag(range.end(), StylePos.SELECTION, "");
    }
}
