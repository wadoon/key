package de.uka.ilkd.key.nui.filter;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uka.ilkd.key.util.Pair;

public class CriterionRange implements Criteria<Pair<Integer, String>> {

    private int before;
    private int after;
    private Criteria<Pair<Integer, String>> criteria;

    public CriterionRange(int before, int after,
            Criteria<Pair<Integer, String>> criteria) {
        this.before = before;
        this.after = after;
        this.criteria = criteria;
    }

    @Override
    public List<Pair<Integer, String>> meetCriteria(
            List<Pair<Integer, String>> entities) {
        List<Pair<Integer, String>> childlist = criteria.meetCriteria(entities);
        List<Pair<Integer, String>> filtered = new LinkedList<Pair<Integer, String>>();

        // get X before and after
        ArrayList<Integer> filterFor = new ArrayList<>();
        for (Pair<Integer, String> lineInfo : childlist) {
            int index = lineInfo.first;
            IntStream.range(0, before).forEach(n -> {
                int d = index - before + n;
                if (d > 0)
                    filterFor.add(d);
            });
            // add the element itself
            filterFor.add(lineInfo.first);
            IntStream.range(0, after).forEach(n -> {
                int d = index + (n + 1);
                if (d < entities.size())
                    filterFor.add(d);
            });
        }

        // remove double entries
        for (Integer i : filterFor.stream().distinct()
                .collect(Collectors.toList())) {
            for (Pair<Integer, String> pair : entities) {
                if (pair.first.equals(i))
                    filtered.add(pair);
            }
        }
        return filtered;
    }

}
