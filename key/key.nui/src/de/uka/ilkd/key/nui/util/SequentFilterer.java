package de.uka.ilkd.key.nui.util;

import java.util.ArrayList;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uka.ilkd.key.nui.model.PrintFilter;

public class SequentFilterer {
    public static ArrayList<Integer> applyFilter(String proofString,
            PrintFilter filter) {
        if(filter.getSearchString() == null){
            return new ArrayList<>();
        }
        
        ArrayList<Integer> filterFor = new ArrayList<>();
        String[] lines = proofString.split("\n");
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(filter.getSearchString())) {
                int index = i;
                IntStream.range(0, filter.getBefore()).forEach(n -> {
                    int d = index - filter.getBefore() + n;
                    if (d > 0)
                        filterFor.add(d);
                });
                filterFor.add(i);
                IntStream.range(0, filter.getAfter()).forEach(n -> {
                    int d = index + (n + 1);
                    if (d < lines.length)
                        filterFor.add(d);
                });
            }
        }
        return new ArrayList<>(
                filterFor.stream().distinct().collect(Collectors.toList()));
    }
}
