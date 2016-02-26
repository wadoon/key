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
import de.uka.ilkd.key.util.Pair;

/**
 * 
 * @author Benedikt Gross
 *
 */
public class CriterionAstScope implements Criteria<Integer> {

    private Criteria<Integer> criteria;
    private InitialPositionTable positionTable;
    private IdentitySequentPrintFilter identitySequentFilter;
    private String[] originalLines;

    public CriterionAstScope(Criteria<Integer> criteria,
            InitialPositionTable positionTable,
            IdentitySequentPrintFilter identitySequentFilter,
            String[] originalLines) {
        this.criteria = criteria;
        this.positionTable = positionTable;
        this.identitySequentFilter = identitySequentFilter;
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

        charIndex = 0;
        lineIndex = 0;
        for (Pair<Integer, Integer> range : ranges) {

            /*
             * resolve line position to char index to get the underlying subTerm
             * then get bounds of this subTerm then resolve this char index pack
             * to a line position
             */

            // add previous subTerm bounds
            PosInSequent previous = positionTable.getPosInSequent(
                    getCharIndex(range.first, entities), identitySequentFilter);
            lines.addAll(
                    IntStream
                            .range(getLineIndex(previous.getBounds().start()),
                                    range.first)
                            .boxed().collect(Collectors.toList()));

            // add following subTerm bounds
            PosInSequent following = positionTable.getPosInSequent(
                    getCharIndex(range.second, entities),
                    identitySequentFilter);
            lines.addAll(IntStream
                    .range(range.second,
                            getLineIndex(following.getBounds().end()))
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
            idx += originalLines[line].length();
            if (idx >= currentChar)
                return line;
        }
        return -1;
    }

    // used in getCharIndex
    int charIndex = 0;
    int lineIndex = 0;

    // XXX performance dude ..
    private int getCharIndex(int currentLine, List<Integer> entities) {
        // advance charIndex until current line is reached
        while (lineIndex < entities.size()) {
            if (entities.get(lineIndex) == currentLine) {
                String string = originalLines[lineIndex];
                // get first non-whitespace
                for (int i = 0; i < string.length(); i++) {
                    if (!Character.isSpaceChar(string.charAt(i)))
                        break;
                    charIndex++;
                }
                break;
            }
            charIndex += originalLines[lineIndex].length();
            lineIndex++;
        }
        return charIndex;
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
