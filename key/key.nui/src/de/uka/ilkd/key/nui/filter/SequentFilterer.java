package de.uka.ilkd.key.nui.filter;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.util.Pair;

public class SequentFilterer {
    
    public static ArrayList<Integer> applyFilter(String proofString,
            Criteria<Pair<Integer,String>> filterCriteria) {
        if (filterCriteria == null) {
            throw new IllegalArgumentException("filterCriteria");
        }

        String[] lines = proofString.split("\n");

        List<Pair<Integer, String>> textLines = new LinkedList<>();
        for (int i = 0; i < lines.length; i++) {
            textLines.add(new Pair<Integer, String>(i, lines[i]));
        }
        textLines = filterCriteria.meetCriteria(textLines);

        ArrayList<Integer> indices = new ArrayList<>();
        for (Pair<Integer, String> pair : textLines)
            indices.add(pair.first);
        return indices;
    }
}
