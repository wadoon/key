package de.uka.ilkd.key.nui.filter;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * A criteria that adds X entities before and X entities after all entities left
 * over by its child criteria.
 * 
 * @author Benedikt Gross
 *
 */
public class CriterionRange implements Criterion<Integer> {

    private int before;
    private int after;
    private Criterion<Integer> criteria;
    private String[] originalLines;

    /**
     * Instantiates a new range criterion
     * @param criteria
     *            A distinct and ordered entity list
     * @param before
     *            How many entities before a match should be added.
     * @param after
     *            How many entities after a match should be added.
     */
    public CriterionRange(Criterion<Integer> criteria, int before, int after,
            String[] originalLines) {
        this.before = before;
        this.after = after;
        this.criteria = criteria;
        if (originalLines != null) {
            this.originalLines = (String[]) originalLines.clone();
        }
    }

    @Override
    public List<Integer> meetCriteria(List<Integer> lines) {
        List<Integer> childlist = criteria.meetCriteria(lines);

        // get X before and after
        ArrayList<Integer> filterFor = new ArrayList<>();
        for (Integer lineIndex : childlist) {
            IntStream.range(0, before).forEach(n -> {
                int d = lineIndex - before + n;
                if (d >= 0)
                    filterFor.add(d);
            });
            // add the element itself
            filterFor.add(lineIndex);
            IntStream.range(0, after).forEach(n -> {
                int d = lineIndex + (n + 1);
                if (d < originalLines.length)
                    filterFor.add(d);
            });
        }

        // remove double entries
        return filterFor.stream().distinct().collect(Collectors.toList());
    }

}
