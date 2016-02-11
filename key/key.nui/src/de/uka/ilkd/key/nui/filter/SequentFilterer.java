package de.uka.ilkd.key.nui.filter;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uka.ilkd.key.util.Pair;

public class SequentFilterer {
    public static ArrayList<Integer> applyFilter(String proofString,
            PrintFilter filter) {
        if (filter.getCriteria() == null) {
            return new ArrayList<>();
        }
        
        String[] lines = proofString.split("\n");

        List<Pair<Integer, String>> textLines = new LinkedList<>();
        for (int i = 0; i < lines.length; i++) {
            textLines.add(new Pair<Integer, String>(i, lines[i]));
        }
        textLines = filter.getCriteria().meetCriteria(textLines);

        ArrayList<Integer> filterFor = new ArrayList<>();
        for(Pair<Integer, String> lineInfo : textLines){
            int index = lineInfo.first;
            IntStream.range(0, filter.getBefore()).forEach(n -> {
                int d = index - filter.getBefore() + n;
                if (d > 0)
                    filterFor.add(d);
            });
            filterFor.add(lineInfo.first);
            IntStream.range(0, filter.getAfter()).forEach(n -> {
                int d = index + (n + 1);
                if (d < lines.length)
                    filterFor.add(d);
            });
        }

        return new ArrayList<>(
                filterFor.stream().distinct().collect(Collectors.toList()));
    }
}
