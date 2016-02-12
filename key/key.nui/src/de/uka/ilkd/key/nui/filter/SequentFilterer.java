package de.uka.ilkd.key.nui.filter;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.util.Pair;

public class SequentFilterer {
    
    public static ArrayList<Integer> applyFilter(String proofString,
            PrintFilter filter) {
        Criteria<Pair<Integer, String>> criteria = createCriteria(filter);

        if (criteria == null) {
            return new ArrayList<>();
        }

        String[] lines = proofString.split("\n");

        List<Pair<Integer, String>> textLines = new LinkedList<>();
        for (int i = 0; i < lines.length; i++) {
            textLines.add(new Pair<Integer, String>(i, lines[i]));
        }
        textLines = criteria.meetCriteria(textLines);

        ArrayList<Integer> indices = new ArrayList<>();
        for (Pair<Integer, String> pair : textLines)
            indices.add(pair.first);
        return indices;
    }

    private static Criteria<Pair<Integer, String>> createCriteria(PrintFilter filter) {
        Criteria<Pair<Integer, String>> criteria;
        if (filter.getIsUserCriteria())
            criteria = new CriterionContainsString(filter.getSearchText());
        else
            criteria = filter.getSelectionCriteria();

        if (filter.getBefore() != 0 || filter.getAfter() != 0) {
            criteria = new CriterionRange(filter.getBefore(), filter.getAfter(),
                    criteria);
        }

        // apply invert as last
        if (filter.getInvert())
            criteria = new NotCriteria<>(criteria);

        return criteria;
    }
}
