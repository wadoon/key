package de.uka.ilkd.key.nui.printer;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.nui.Context;
import de.uka.ilkd.key.nui.filter.PrintFilter.FilterLayout;
import de.uka.ilkd.key.nui.util.CssFileHandler;
import de.uka.ilkd.key.nui.util.NUIConstants;
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
 * styles the SequentText as HTML Text
 * 
 * @author Maximilian Li
 * @author Victor Schuemmer
 */
public class SequentPrinter {
    private String proofString;
    private CssFileHandler cssFileHandler;
    private PositionTable posTable;
    private Sequent sequent;
    private boolean useRegex = false;

    private PrintDictionary dictionary = new PrintDictionary();
    private ArrayList<Integer> lessThenList = new ArrayList<Integer>();
    private ArrayList<Integer> filterCollapseIndicator = new ArrayList<Integer>();

    private Context context;

    /**
     * Constructor that sets the given arguments.
     * 
     * @param cssFileHandler
     *            {@link CssFileHandler}
     * @param posTable
     *            {@link PositionTable}
     * @param context
     *            {@link Context}
     */
    public SequentPrinter(CssFileHandler cssFileHandler, PositionTable posTable,
            Context context) {
        this.cssFileHandler = cssFileHandler;
        this.setPosTable(posTable);
        this.context = context;
    }

    /**
     * Prints a sequent as HTML with styling.
     * 
     * @return HTML Text with default style
     */
    public String printProofString() {
        int offset = 0;
        StringBuilder sb = new StringBuilder(proofString);

        List<Pair<Integer, String>> tagList = dictionary.getTagList();
        int listPointer = 0;
        String tag;

        // Iterate to Length+1 to Append CollapsedIndicator if all is hidden
        for (int i = 0; i < proofString.length() + 1; i++) {
            // Insert StyleTags at i
            while (listPointer < tagList.size()
                    && tagList.get(listPointer).first == i) {
                tag = tagList.get(listPointer).second;
                sb.insert(i + offset, tag);
                offset += tag.length();
                listPointer++;
            }
            // Insert CollapsedIndicator at i
            if (filterCollapseIndicator.contains(i)) {
                sb.insert(i + offset, "...\n");
                offset += 4;
            }
            // HTML Formatting at i
            if (lessThenList.contains(i)) {
                sb.replace(i + offset, i + offset + 1, "&lt;");
                offset += 3;
            }
        }

        String html = sb.toString();
        context.setSequentHtml(html);
        return toHTML(html);
    }

    /**
     * gets the HighlightingRange from the InitialPositionTable for a Position
     * 
     * @param pos
     *            the Position of the Term to be highlighted
     * @return the Range of the Term
     */
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

    /**
     * Applies highlighting for the last applied rule.
     * 
     * @param app
     *            the last applied {@link RuleApp Rule Application}
     */
    public void applyRuleAppHighlighting(RuleApp app) {
        if (app.posInOccurrence() != null) {
            Range r = getHighlightRange(app.posInOccurrence());
            putStyleTags(r.start(), r.end(), HighlightType.RULEAPP,
                    NUIConstants.RULE_APP_TAG);
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
     *            The taclet app for which the of the formulae should be
     *            highlighted.
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
            putStyleTags(r.start(), r.end(), HighlightType.RULEAPP,
                    NUIConstants.IF_FORMULA_TAG);
        }
    }

    /**
     * highlights if Instances
     * 
     * @param bapp
     */
    private void highlightIfInsts(IBuiltInRuleApp bapp) {
        final ImmutableList<PosInOccurrence> ifs = bapp.ifInsts();
        for (PosInOccurrence pio : ifs) {
            Range r = getHighlightRange(pio);
            putStyleTags(r.start(), r.end(), HighlightType.RULEAPP,
                    NUIConstants.IF_INST_TAG);
        }
    }

    /**
     * Applies mouseover Highlighting for the given range.
     * 
     * @param range
     *            the {@link Range} Object specifying the proof string part to
     *            be highlighted
     */
    public void applyMouseHighlighting(Range range) {
        removeMouseHighlighting();
        putStyleTags(range.start(), range.end(), HighlightType.MOUSE,
                NUIConstants.MOUSE_TAG);
    }

    /**
     * Styles the text according to given filter.
     * 
     * @param indicesOfUnfilteredLines
     *            a List of Lines that should not be filtered out
     * @param layout
     *            the FilterLayout
     */
    public void applyFilter(ArrayList<Integer> indicesOfUnfilteredLines,
            FilterLayout layout) {
        // remove old Filter styling
        removeFilter();
        // get line information
        String[] lines = proofString.split("\n");

        int styleStart = 0;

        // Iterate over the lines
        for (int i = 0; i < lines.length; i++) {
            // Compute Endindex of Line
            int styleEnd = styleStart + lines[i].length() + 1;

            // If line is in list apply styles
            if (!indicesOfUnfilteredLines.contains(i)) {
                switch (layout) {
                case Minimize:
                    minimizeLine(styleStart, styleEnd);
                    break;
                case Collapse:
                default:
                    // Add collapsed indicator if collapsed Block ends, or the
                    // last line is reached
                    if (indicesOfUnfilteredLines.contains(i + 1)
                            || i == lines.length - 1) {
                        filterCollapseIndicator.add(styleEnd);
                    }
                    collapseLine(styleStart, styleEnd);
                    break;
                }
            }
            styleStart = styleEnd;
        }

        // Append CollapsedIndicator if all is hidden
        if ((indicesOfUnfilteredLines == null
                || indicesOfUnfilteredLines.isEmpty())
                && layout == FilterLayout.Collapse) {
            filterCollapseIndicator.add(proofString.length());
        }
    }

    /**
     * Adds collapsed style for the line defined by the indices.
     * 
     * @param lineStart
     *            startIndex of line
     * @param lineEnd
     *            endIndex of line
     */
    private void collapseLine(int lineStart, int lineEnd) {
        putStyleTags(lineStart, lineEnd, HighlightType.FILTER,
                NUIConstants.FILTER_COLLAPSED_TAG);
    }

    /**
     * Adds minimized style for the line defined by the indices.
     * 
     * @param lineStart
     *            startIndex of line
     * @param lineEnd
     *            endIndex of line
     */
    private void minimizeLine(int lineStart, int lineEnd) {
        putStyleTags(lineStart, lineEnd, HighlightType.FILTER,
                NUIConstants.FILTER_MINIMIZED_TAG);
    }

    /**
     * Removes all the applied styling by the filter functions.
     */
    private void removeFilter() {
        dictionary.removeAllTypeTags(HighlightType.FILTER);
        filterCollapseIndicator.clear();
    }

    /**
     * To be used to add an opening <span class="..."> tag. Do not forget to
     * call putCloseTag!
     * 
     * @param index
     *            position inside the proof string
     * @param highlightType
     *            the {@link HighlightType}
     * @param tag
     *            the opening tag constant
     */
    private void putOpenTag(int index, HighlightType highlightType,
            String tag) {
        dictionary.putOpenTag(index, highlightType, tag);
    }

    /**
     * Puts an opening tag at the start position and a closing one at the end
     * position.
     * 
     * @param start
     *            start position inside the proof string
     * @param end
     *            end position inside the proof string
     * @param type
     *            the {@link HighlightType}
     * @param tag
     *            the opening tag constant
     */
    private void putStyleTags(int start, int end, HighlightType type,
            String tag) {
        putOpenTag(start, type, tag);
        putCloseTag(end, type);
    }

    /**
     * To be used to add a closing </span> tag. Do not forget to call
     * putOpenTag!
     * 
     * @param index
     *            position inside the proof string
     * @param highlightType
     *            the {@link HighlightType}
     */
    private void putCloseTag(int index, HighlightType highlightType) {
        dictionary.putCloseTag(index, highlightType);
    }

    /**
     * Removes all the mouseover highlighting currently applied.
     */
    public void removeMouseHighlighting() {
        dictionary.removeAllTypeTags(HighlightType.MOUSE);
    }

    /**
     * Set the String used for free text search highlighting.
     * 
     * @param searchString
     *            the free text search string
     * @return {@link ArrayList} filled with indices of all matches.
     */
    public List<Integer> applyFreetextSearch(String searchString) {
        // remove old Search Highlighting
        removeSearchIndices();
        ArrayList<Integer> result = new ArrayList<>();
        if (!searchString.isEmpty()) {
            if (useRegex) {
                // try-catch block for incomplete Regex Patterns
                try {
                    Pattern pattern = Pattern.compile(searchString);
                    Matcher matcher = pattern.matcher(proofString);

                    // Iterate over all findings and add to TreeMap
                    while (matcher.find()) {
                        result.add(matcher.start());
                        // Check all occurrences
                        putStyleTags(matcher.start(), matcher.end(),
                                HighlightType.SEARCH,
                                NUIConstants.HIGHLIGHTED_TAG);
                    }
                }
                catch (RuntimeException e) {
                    return result;
                }

            }
            else {
                // Find indices of all matches. Put in Map. Put in ArrayList for
                // removal
                for (int i = -1; (i = proofString.indexOf(searchString,
                        i + 1)) != -1;) {
                    result.add(i);
                    putStyleTags(i, i + searchString.length(),
                            HighlightType.SEARCH, NUIConstants.HIGHLIGHTED_TAG);
                }
            }
        }
        return result;
    }

    /**
     * Iterates over the search indices {@link ArrayList}. Uses this information
     * to remove references in Styling {@link TreeMap}.
     */
    private void removeSearchIndices() {
        dictionary.removeAllTypeTags(HighlightType.SEARCH);
    }

    /**
     * @param proofString
     *            the proofString to set
     */
    public void setProofString(String proofString) {
        this.proofString = proofString;

        // As a new ProofString means old styling Info is deprecated.
        lessThenList.clear();
        dictionary.clear();

        setLessThenIndices(proofString);
        applySyntaxHighlighting();

    }

    /**
     * Adds the indices of all the "<" signs inside the given String for
     * escaping.
     * 
     * @param string
     *            the string to be escaped
     */
    private void setLessThenIndices(String string) {
        // Find indices of all matches. Put in Map. Put in ArrayList for
        // removal
        for (int i = -1; (i = proofString.indexOf("<", i + 1)) != -1;) {
            lessThenList.add(i);
        }
    }

    /**
     * @param posTable
     *            the {@link PositionTable} to set
     */
    public void setPosTable(PositionTable posTable) {
        this.posTable = posTable;
    }

    /**
     * Puts Syntax Styling Info in tagsAtIndex Map.
     */
    private void applySyntaxHighlighting() {
        Map<String, String> classMap = context.getXmlReader().getClassMap();
        Map<String, Boolean> classEnabledMap = context.getXmlReader()
                .getClassEnabledMap();

        if (!(posTable instanceof InitialPositionTable)) {
            throw new AssertionError(
                    "Unexpected type (should be InitialPositionTable: "
                            + posTable);
        }
        InitialPositionTable initPos = (InitialPositionTable) posTable;

        IdentitySequentPrintFilter filter = new IdentitySequentPrintFilter(
                sequent);

        Class<? extends Object> lastClass = null;
        boolean openedTag = false;

        // Iterate over String. Insert Tags according to class.
        for (int i = 0; i < proofString.length(); i++) {
            PosInSequent pos = initPos.getPosInSequent(i, filter);

            // Close Tag on Whitespace, if it was opened before
            if ((proofString.charAt(i) == ' '
                    || proofString.charAt(i) == '\n')) {
                if (openedTag) {
                    putCloseTag(i, HighlightType.SYNTAX);

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
                    String className = op.getClass().getSimpleName();
                    // Open First Tag
                    if (lastClass == null && classMap.containsKey(className)
                            && classEnabledMap.get(className)) {

                        putOpenTag(i, HighlightType.SYNTAX,
                                classMap.get(className));

                        openedTag = true;
                        lastClass = op.getClass();
                    }

                    // If Class changed, close the existing Tag, open new one
                    else if (lastClass != null && lastClass != op.getClass()) {

                        putCloseTag(i, HighlightType.SYNTAX);

                        openedTag = false;
                        if (classMap.containsKey(className)
                                && classEnabledMap.get(className)) {

                            putOpenTag(i, HighlightType.SYNTAX,
                                    classMap.get(className));
                            lastClass = op.getClass();
                            openedTag = true;
                        }
                        // Syso to let the user know the AST Class is unknown
                        else {
                            lastClass = null;
                            openedTag = false;
                            if (!classMap.containsKey(className)) {
                                System.out.println("");
                                System.out.println(
                                        "The following Class does not exist in the ClassDictionary");
                                System.out.println("EXPRESSION: " + op);
                                System.out.println("CLASS: " + className);
                                System.out.println("");
                            }
                        }
                    }

                }
            }
        }
    }

    /**
     * Converts the input String to HTML tagged text.
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
     * Sets useRegex.
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

    /**
     * applies the MouseSelection Visuals from the Filter
     * 
     * @param range
     *            the Range for the Selection
     */
    public void applySelection(Range range) {
        putStyleTags(range.start(), range.end(), HighlightType.SELECTION,
                NUIConstants.FILTER_SELECTION_TAG);
    }

    /**
     * removes the MouseSelection Visuals from the Filter
     * 
     * @param range
     *            the Range for the Selection
     */
    public void removeSelection(Range range) {
        dictionary.removeSingleStyleTag(range.start(), range.end(),
                HighlightType.SELECTION);
    }
}
