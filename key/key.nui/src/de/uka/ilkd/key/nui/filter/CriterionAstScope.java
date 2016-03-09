package de.uka.ilkd.key.nui.filter;

import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uka.ilkd.key.pp.InitialPositionTable;
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
                    .rangeForIndex(LineToPrintedProofPosition
                            .getCharIndex(range.first, originalLines)
                            + LineToPrintedProofPosition.getFirstNonWhitespace(
                                    originalLines[range.first]));
            lines.addAll(IntStream
                    .range(LineToPrintedProofPosition
                            .getLineIndex(previous.start(), originalLines),
                    LineToPrintedProofPosition.getLineIndex(previous.end(),
                            originalLines) + 1)
                    .boxed().collect(Collectors.toList()));

            // add following subTerm bounds, use last character of the last line
            // of this range as charIndex
            Range following = positionTable
                    .rangeForIndex(LineToPrintedProofPosition
                            .getCharIndex(range.second, originalLines)
                            // decrease char index by two to get rid of
                            // line-break and last continuing character (e.g. a
                            // comma)
                            + originalLines[range.second].length() - 2);
            lines.addAll(IntStream
                    .range(LineToPrintedProofPosition
                            .getLineIndex(following.start(), originalLines),
                    LineToPrintedProofPosition.getLineIndex(following.end(),
                            originalLines) + 1)
                    .boxed().collect(Collectors.toList()));
        }

        // distinct and reorder
        List<Integer> distinctLines = lines.stream().distinct()
                .collect(Collectors.toList());
        return distinctLines;
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
