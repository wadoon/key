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
public class CriterionAstScope implements Criteria<Pair<Integer, String>> {

    Criteria<Pair<Integer, String>> criteria;
    InitialPositionTable positionTable;
    IdentitySequentPrintFilter identitySequentFilter;

    public CriterionAstScope(Criteria<Pair<Integer, String>> criteria,
            InitialPositionTable positionTable,
            IdentitySequentPrintFilter identitySequentFilter) {
        this.criteria = criteria;
        this.positionTable = positionTable;
        this.identitySequentFilter = identitySequentFilter;
    }

    @Override
    public List<Pair<Integer, String>> meetCriteria(
            List<Pair<Integer, String>> entities) {
        List<Pair<Integer, String>> childList = criteria.meetCriteria(entities);

        if (childList.size() == 0)
            return new LinkedList<>();

        // get ranges
        List<Pair<Integer, Integer>> ranges = new LinkedList<>();
        int lastRangeStart = childList.get(0).first;
        int index = lastRangeStart;
        for (Pair<Integer, String> pair : childList) {
            if (pair.first - index > 1) {
                // if there is a gap, finish the range and start a new one
                ranges.add(new Pair<Integer, Integer>(lastRangeStart, index));
                lastRangeStart = pair.first;
            }
            index = pair.first;
        }

        // for each range, get the previous and following AST elements that were
        // hit

        List<Integer> lines = new LinkedList<>();
        childList.forEach(p -> lines.add(p.first));

        charIndex = 0;
        lineIndex = 0;
        for (Pair<Integer, Integer> pair : ranges) {

            /*
             * resolve line position to char index to get the underlying subTerm
             * then get bounds of this subTerm then resolve this char index pack
             * to a line position
             */

            // add previous subTerm bounds
            PosInSequent previous = positionTable.getPosInSequent(
                    getCharIndex(pair.first, entities), identitySequentFilter);
            lines.addAll(
                    IntStream
                            .range(getLineIndex(previous.getBounds().start(),
                                    entities), pair.first)
                            .boxed().collect(Collectors.toList()));

            // add following subTerm bounds
            PosInSequent following = positionTable.getPosInSequent(
                    getCharIndex(pair.second, entities), identitySequentFilter);
            lines.addAll(
                    IntStream
                            .range(getLineIndex(following.getBounds().end(),
                                    entities), pair.second)
                            .boxed().collect(Collectors.toList()));
        }

        // distinct and reorder
        List<Integer> distinctLines = lines.stream().distinct()
                .collect(Collectors.toList());

        List<Pair<Integer, String>> list = new LinkedList<>();
        distinctLines.forEach(i -> list.add(searchIndex(i, entities)));
        return list;
    }

    // XXX performance dude ..
    private int getLineIndex(int currentChar,
            List<Pair<Integer, String>> entities) {
        int idx = 0;
        for (Pair<Integer, String> line : entities) {
            idx += line.second.length();
            if (idx > currentChar)
                return line.first;
        }
        return -1;
    }

    // used in getCharIndex
    int charIndex = 0;
    int lineIndex = 0;

    // XXX performance dude ..
    private int getCharIndex(int currentLine,
            List<Pair<Integer, String>> entities) {
        // advance charIndex until current line is reached
        while (lineIndex < entities.size()) {
            if (entities.get(lineIndex).first == currentLine) {
                String string = entities.get(lineIndex).second;
                // get first non-whitespace
                for (int i = 0; i < string.length(); i++) {
                    if (!Character.isSpaceChar(string.charAt(i)))
                        break;
                    charIndex++;
                }
                break;
            }
            charIndex += entities.get(lineIndex).second.length();
            lineIndex++;
        }
        return charIndex;
    }

    // XXX performance dude ..
    private Pair<Integer, String> searchIndex(int index,
            List<Pair<Integer, String>> list) {
        for (Pair<Integer, String> pair : list) {
            if (pair.first == index)
                return pair;
        }
        return null;
    }
}
