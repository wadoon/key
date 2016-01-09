package de.uka.ilkd.key.nui.util;

import java.util.ArrayList;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uka.ilkd.key.nui.model.PrintFilter;

public class SequentFilterer {
    public static ArrayList<Integer> ApplyFilter(String proofString,
            PrintFilter filter) {
        ArrayList<Integer> filterFor = new ArrayList<>();
        String[] lines = proofString.split("\n");
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].contains(filter.getSearchString())){
                int index = i;
                IntStream.range(0, filter.getBefore()).forEach(n -> filterFor.add(index - (n+1)));
                IntStream.range(0, filter.getAfter()).forEach(n -> filterFor.add(index + (n+1)));
                filterFor.add(i);
            }
        }
        return new ArrayList<>(filterFor.stream().distinct().collect(Collectors.toList()));
    }
}
