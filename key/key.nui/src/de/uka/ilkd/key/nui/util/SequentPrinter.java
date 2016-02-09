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
import java.util.Stack;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.nui.model.Context;
import de.uka.ilkd.key.nui.model.PrintFilter;
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

    private TreeSet<Integer> keySet = new TreeSet<Integer>();

    private HashMap<Integer, String[]> openTagsAtIndex = new HashMap<Integer, String[]>();;
    private HashMap<Integer, String[]> closeTagsAtIndex = new HashMap<Integer, String[]>();;

    private ArrayList<Integer> lessThenList = new ArrayList<Integer>();

    private ArrayList<Integer> mouseIndicesOpen = new ArrayList<Integer>();
    private ArrayList<Integer> mouseIndicesClose = new ArrayList<Integer>();
    private ArrayList<Integer> searchIndicesOpen = new ArrayList<Integer>();
    private ArrayList<Integer> searchIndicesClose = new ArrayList<Integer>();
    private ArrayList<Integer> filterIndicesOpen = new ArrayList<Integer>();
    private ArrayList<Integer> filterIndicesClose = new ArrayList<Integer>();

    private static HashMap<Class, String> classMap = new HashMap<>();
    private static HashMap<Class, Boolean> classEnabledMap = new HashMap<>();

    private final static String OPEN_TAG_BEGIN = "<span class=\"";
    private final static String OPEN_TAG_END = "\">";
    private final static String CLOSING_TAG = "</span>";

    private final static String MOUSE_TAG = "mouseover";
    private final static String HIGHLIGHTED_TAG = "highlighted";
    private final static String FILTER_MINIMIZED_TAG = "minimized";
    private final static String FILTER_COLLAPSED_TAG = "collapsed";
    private final static String RULE_APP_TAG = "ruleApp";
    private final static String IF_INST_TAG = "ifInst";
    private final static String IF_FORMULA_TAG = "ifFormula";

    private enum StylePos {
        SYNTAX(4), MOUSE(0), SEARCH(2), FILTER(1), RULEAPP(3);

        private int slotPosition;

        private StylePos(int i) {
            slotPosition = i;
        }
    }

    private Context context;

    /**
     * 
     */
    public SequentPrinter(String cssPath, PositionTable posTable,
            Context context) {
        try {
            readCSS(cssPath);
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        this.setPosTable(posTable);

        this.context = context;

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
        if (classEnabledMap.size() > 0 && classMap.size() > 0) {
            return;
        }
        // Defines if this AST Class shall be highlighted
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Equality.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Function.class, false);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.LocationVariable.class,
                true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Junctor.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.LogicVariable.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Quantifier.class, true);
        classEnabledMap.put(
                de.uka.ilkd.key.logic.op.SortDependingFunction.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Modality.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ObserverFunction.class,
                true);
        classEnabledMap.put(
                de.uka.ilkd.key.logic.op.AbstractSortedOperator.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.AbstractSV.class, true);
        classEnabledMap.put(
                de.uka.ilkd.key.logic.op.AbstractTermTransformer.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ElementaryUpdate.class,
                true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.FormulaSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.IfExThenElse.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.IfThenElse.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ModalOperatorSV.class,
                true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ProgramConstant.class,
                true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ProgramMethod.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ProgramSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.ProgramVariable.class,
                true);
        classEnabledMap.put(
                de.uka.ilkd.key.logic.op.SchemaVariableFactory.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.SkolemTermSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.SubstOp.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.TermLabelSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.TermSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.Transformer.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.UpdateApplication.class,
                true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.UpdateJunctor.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.UpdateSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.VariableSV.class, true);
        classEnabledMap.put(de.uka.ilkd.key.logic.op.WarySubstOp.class, true);

        // Define Style Span for each Class
        classMap.put(de.uka.ilkd.key.logic.op.Equality.class, "equality");
        classMap.put(de.uka.ilkd.key.logic.op.Function.class, "function");
        classMap.put(de.uka.ilkd.key.logic.op.LocationVariable.class,
                "locationVar");
        classMap.put(de.uka.ilkd.key.logic.op.Junctor.class, "junctor");
        classMap.put(de.uka.ilkd.key.logic.op.LogicVariable.class, "logicVar");
        classMap.put(de.uka.ilkd.key.logic.op.Quantifier.class, "quantifier");
        classMap.put(de.uka.ilkd.key.logic.op.SortDependingFunction.class,
                "sortDepFunc");
        classMap.put(de.uka.ilkd.key.logic.op.Modality.class, "modality");
        classMap.put(de.uka.ilkd.key.logic.op.ObserverFunction.class,
                "observerFunc");
        classMap.put(de.uka.ilkd.key.logic.op.AbstractSortedOperator.class,
                "abstractSortOp");
        classMap.put(de.uka.ilkd.key.logic.op.AbstractSV.class, "abstractSV");
        classMap.put(de.uka.ilkd.key.logic.op.AbstractTermTransformer.class,
                "abstractTermTransf");
        classMap.put(de.uka.ilkd.key.logic.op.ElementaryUpdate.class,
                "elemUpdate");
        classMap.put(de.uka.ilkd.key.logic.op.FormulaSV.class, "formulaSV");
        classMap.put(de.uka.ilkd.key.logic.op.IfExThenElse.class,
                "ifExThenElse");
        classMap.put(de.uka.ilkd.key.logic.op.IfThenElse.class, "ifThenElse");
        classMap.put(de.uka.ilkd.key.logic.op.ModalOperatorSV.class,
                "modalOpSV");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramConstant.class,
                "progConst");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramMethod.class, "progMeth");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramSV.class, "progSV");
        classMap.put(de.uka.ilkd.key.logic.op.ProgramVariable.class, "progVar");
        classMap.put(de.uka.ilkd.key.logic.op.SchemaVariableFactory.class,
                "schemaVarFactory");
        classMap.put(de.uka.ilkd.key.logic.op.SkolemTermSV.class,
                "skolemTermSV");
        classMap.put(de.uka.ilkd.key.logic.op.SubstOp.class, "substOp");
        classMap.put(de.uka.ilkd.key.logic.op.TermLabelSV.class, "termLabelSV");
        classMap.put(de.uka.ilkd.key.logic.op.TermSV.class, "termSV");
        classMap.put(de.uka.ilkd.key.logic.op.Transformer.class, "transformer");
        classMap.put(de.uka.ilkd.key.logic.op.UpdateApplication.class,
                "updateApp");
        classMap.put(de.uka.ilkd.key.logic.op.UpdateJunctor.class,
                "updateJunc");
        classMap.put(de.uka.ilkd.key.logic.op.UpdateSV.class, "updateSV");
        classMap.put(de.uka.ilkd.key.logic.op.VariableSV.class, "varSV");
        classMap.put(de.uka.ilkd.key.logic.op.WarySubstOp.class, "warySubstOp");
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

        for (Integer i : keySet) {
            // Apply Close Tags first
            if (closeTagsAtIndex.containsKey(i)) {
                for (int j = 0; j < StylePos.values().length; j++) {
                    insertTag = closeTagsAtIndex.get(i)[j];
                    if (insertTag != null) {
                        sb.insert(i + offset, insertTag);
                        offset += insertTag.length();
                    }
                }
            }
            // Apply OpenTags
            if (openTagsAtIndex.containsKey(i)) {
                for (int j = 0; j < StylePos.values().length; j++) {
                    insertTag = openTagsAtIndex.get(i)[j];
                    if (insertTag != null) {
                        sb.insert(i + offset, insertTag);
                        offset += insertTag.length();
                    }
                }
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
        return toHTML(html);
    }

    private Range getHighlightRange(PosInOccurrence pos) {
        ImmutableList<Integer> path = ((InitialPositionTable) posTable)
                .pathForPosition(pos, new IdentitySequentPrintFilter(sequent));
        return ((InitialPositionTable) posTable).rangeForPath(path);
    }

    public void applyRuleAppHighlighting(RuleApp app) {
        if (app.posInOccurrence() != null) {
            Range r = getHighlightRange(app.posInOccurrence());
            putOpenTag(r.start(), StylePos.RULEAPP, RULE_APP_TAG);
            putCloseTag(r.end(), StylePos.RULEAPP, CLOSING_TAG);
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
            putOpenTag(r.start(), StylePos.RULEAPP, IF_FORMULA_TAG);
            putCloseTag(r.end(), StylePos.RULEAPP, CLOSING_TAG);
            keySet.add(r.start());
            keySet.add(r.end());
        }
    }

    private void highlightIfInsts(IBuiltInRuleApp bapp) {
        final ImmutableList<PosInOccurrence> ifs = bapp.ifInsts();
        for (PosInOccurrence pio : ifs) {
            Range r = getHighlightRange(pio);
            putOpenTag(r.start(), StylePos.RULEAPP, IF_INST_TAG);
            putCloseTag(r.end(), StylePos.RULEAPP, CLOSING_TAG);
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

        String[] openTagArray;
        String[] closeTagArray;
        Stack<String> tagStack = new Stack<>();

        // Check for Overlap inbetween Start and End
        for (int i = range.start(); i <= range.end(); i++) {

            if (openTagsAtIndex.containsKey(i)
                    || closeTagsAtIndex.containsKey(i)) {

                openTagArray = openTagsAtIndex.get(i);
                closeTagArray = closeTagsAtIndex.get(i);

                for (int j = 0; j < StylePos.values().length; j++) {
                    // If closingTag, pop() the last Opened, or resolve
                    if (closeTagArray != null && closeTagArray[j] != null
                            && !closeTagArray[j].isEmpty()
                            && i > range.start()) {
                        if (tagStack.size() == 0) {
                            putCloseTag(i, StylePos.MOUSE, CLOSING_TAG);
                            putOpenTag(i, StylePos.MOUSE, MOUSE_TAG);
                            mouseIndicesOpen.add(i);
                            mouseIndicesClose.add(i);
                        }
                        else {
                            tagStack.pop();
                        }
                    }
                    // If openTag, push it on the stack
                    if (openTagArray != null && openTagArray[j] != null
                            && !openTagArray[j].isEmpty() && i < range.end()) {
                        tagStack.push(openTagArray[j]);
                    }
                }
            }
        }

        // Insert the MouseOverTags themselves
        putOpenTag(range.start(), StylePos.MOUSE, MOUSE_TAG);
        mouseIndicesOpen.add(range.start());

        putCloseTag(range.end(), StylePos.MOUSE, CLOSING_TAG);
        mouseIndicesClose.add(range.end());

        // If there is an opened Tag inside the range after mouse is closed,
        // resolve the overlap by closing it and opening it again on the outside
        // of the mouseover
        if (tagStack.size() > 0) {
            System.out.println("LAST CLOSE & OPEN");
            putCloseTag(range.end(), StylePos.MOUSE, CLOSING_TAG);
            putTag(range.end(), StylePos.MOUSE, tagStack.pop(),
                    openTagsAtIndex);
            mouseIndicesOpen.add(range.end());
        }
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
        putOpenTag(lineStart, StylePos.FILTER, FILTER_COLLAPSED_TAG);
        putCloseTag(lineEnd, StylePos.FILTER, CLOSING_TAG);

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
        putOpenTag(lineStart, StylePos.FILTER, FILTER_MINIMIZED_TAG);
        putCloseTag(lineEnd, StylePos.FILTER, CLOSING_TAG);

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
            HashMap<Integer, String[]> map) {
        String[] mapValue = map.get(index);
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
            map.put(index, new String[StylePos.values().length]);
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
    private HashMap<Integer, String[]> putOpenTag(int index, StylePos arrayPos,
            String tag) {
        if (tag.isEmpty()) {
            putTag(index, arrayPos, tag, openTagsAtIndex);
        }
        else {
            putTag(index, arrayPos,
                    OPEN_TAG_BEGIN.concat(tag).concat(OPEN_TAG_END),
                    openTagsAtIndex);
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
    private HashMap<Integer, String[]> putCloseTag(int index, StylePos arrayPos,
            String tag) {
        putTag(index, arrayPos, tag, closeTagsAtIndex);
        return closeTagsAtIndex;
    }

    /**
     * removes all the Mouseover Highlighting currently applied.
     */
    public void removeMouseHighlighting() {
        if (mouseIndicesClose != null) {
            for (Iterator<Integer> iterator = mouseIndicesOpen
                    .iterator(); iterator.hasNext();) {
                int index = (int) iterator.next();
                putOpenTag(index, StylePos.MOUSE, "");
            }
            for (Iterator<Integer> iterator = mouseIndicesClose
                    .iterator(); iterator.hasNext();) {
                int index = (int) iterator.next();
                putCloseTag(index, StylePos.MOUSE, "");
            }

            mouseIndicesOpen.clear();
            mouseIndicesClose.clear();

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
                                HIGHLIGHTED_TAG);
                        putCloseTag(matcher.end(), StylePos.SEARCH,
                                CLOSING_TAG);

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
                    putOpenTag(i, StylePos.SEARCH, HIGHLIGHTED_TAG);
                    putCloseTag(i + searchString.length(), StylePos.SEARCH,
                            CLOSING_TAG);

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
        boolean openedTag = false;

        // Iterate over String. Insert Tags according to class.
        for (int i = 0; i < proofString.length(); i++) {
            PosInSequent pos = initPos.getPosInSequent(i, filter);

            // Close Tag on Whitespace, if it was opened before
            if ((proofString.charAt(i) == ' '
                    || proofString.charAt(i) == '\n')) {
                if (openedTag) {
                    putCloseTag(i, StylePos.SYNTAX, CLOSING_TAG);
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
                    if (lastClass == null && classMap.containsKey(op.getClass())
                            && classEnabledMap.get(op.getClass())) {

                        putOpenTag(i, StylePos.SYNTAX,
                                classMap.get(op.getClass()));
                        keySet.add(i);

                        openedTag = true;
                        lastClass = op.getClass();
                    }

                    // If Class changed, close the existing Tag, open new one
                    else if (lastClass != null && lastClass != op.getClass()) {

                        putCloseTag(i, StylePos.SYNTAX, CLOSING_TAG);
                        keySet.add(i);

                        openedTag = false;
                        if (classMap.containsKey(op.getClass())
                                && classEnabledMap.get(op.getClass())) {

                            putOpenTag(i, StylePos.SYNTAX,
                                    classMap.get(op.getClass()));
                            keySet.add(i);
                            lastClass = op.getClass();
                            openedTag = true;
                        }
                        // Syso to let the user know the AST Class is unknown
                        else {
                            lastClass = null;
                            openedTag = false;
                            if (!classMap.containsKey(op.getClass())) {
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
