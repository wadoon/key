package de.uka.ilkd.key.nui.filter;

import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.util.Pair;

/**
 * 
 * @author Benedikt Gross
 *
 */
public class CriterionAstScope implements Criterion<Integer> {

    private Criterion<Integer> criteria;
    private InitialPositionTable positionTable;
    private String[] originalLines;

    public CriterionAstScope(Criterion<Integer> criteria,
            InitialPositionTable positionTable, String[] originalLines) {
        this.criteria = criteria;
        this.positionTable = positionTable;
        this.originalLines = originalLines;
    }

    @Override
    public List<Integer> meetCriteria(List<Integer> entities) {
        List<Integer> lines = criteria.meetCriteria(entities);

        if (lines.size() == 0)
            return new LinkedList<>();

        // for each range, get the previous and following AST elements that were
        // hit

        List<Pair<Integer, Integer>> ranges = getRanges(lines);
        for (Pair<Integer, Integer> range : ranges) {

            // add previous subTerm bounds, use the first non-white character of
            // the first line of this range as charIndex
            Range previous = positionTable
                    .rangeForIndex(getCharIndex(range.first)
                            + getFirstNonWhitespace(range.first));
            lines.addAll(
                    IntStream.range(getLineIndex(previous.start()), range.first)
                            .boxed().collect(Collectors.toList()));

            // add following subTerm bounds, use last character of the last line
            // of this range as charIndex
            Range following = positionTable
                    .rangeForIndex(getCharIndex(range.second)
                            + originalLines[range.second].length() - 1);
            lines.addAll(IntStream
                    .range(range.second + 1, getLineIndex(following.end()) + 1)
                    .boxed().collect(Collectors.toList()));
        }

        // distinct and reorder
        List<Integer> distinctLines = lines.stream().distinct()
                .collect(Collectors.toList());
        return distinctLines;
    }

    private int getLineIndex(int currentChar) {
        int idx = 0;
        for (int line = 0; line < originalLines.length; line++) {
            // add + 1 to count for the line-break at the end (thanks to max)
            idx += originalLines[line].length() + 1;
            if (idx > currentChar)
                return line;
        }
        return -1;
    }

    private int getFirstNonWhitespace(int lineIndex) {
        String line = originalLines[lineIndex];
        for (int notwhite = 0; notwhite < line.length(); notwhite++) {
            if (!Character.isSpaceChar(line.charAt(notwhite))) {
                // return the first non-whitespace char of this line
                return notwhite;
            }
        }
        return 0;
    }

    private int getCharIndex(int lineIndex) {
        int charIndex = 0;
        for (int i = 0; i < originalLines.length; i++) {
            if (i == lineIndex) {
                return charIndex;
            }
            // add + 1 to count for the line-break at the end (thanks to max)
            charIndex += originalLines[i].length() + 1;
        }
        return -1;
    }

    private List<Pair<Integer, Integer>> getRanges(List<Integer> lines) {
        // detect continuous indices (ranges)
        List<Pair<Integer, Integer>> ranges = new LinkedList<>();
        int lastRangeStart = lines.get(0);
        int index = lastRangeStart;
        for (Integer lineIndex : lines) {
            if (lineIndex - index > 1) {
                // if there is a gap, finish the range and start a new one
                ranges.add(new Pair<Integer, Integer>(lastRangeStart, index));
                lastRangeStart = lineIndex;
            }
            index = lineIndex;
        }
        // add last open range at the end
        ranges.add(new Pair<Integer, Integer>(lastRangeStart, index));
        return ranges;
    }
}
