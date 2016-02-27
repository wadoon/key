package de.uka.ilkd.key.nui.filter;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.util.Pair;

/**
 * A criteria that meets any line that contains the search text.
 * 
 * @author Benedikt Gross
 */
public class CriterionContainsString implements Criteria<Integer> {

    private String searchText;
    private String[] originalLines;

    public CriterionContainsString(String searchText, String[] originalLines) {
        if (searchText == null)
            throw new IllegalArgumentException("searchText");
        this.searchText = searchText;
        this.originalLines = originalLines;
    }

    @Override
    public List<Integer> meetCriteria(List<Integer> lines) {
        List<Integer> list = new LinkedList<>();
        for (Integer lineIndex : lines) {
            if (originalLines[lineIndex] != null
                    && originalLines[lineIndex].contains(searchText)) {
                list.add(lineIndex);
            }
        }
        return list;
    }

}
