package de.uka.ilkd.key.nui.filter;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.util.Pair;

public class CriterionContainsString
        implements Criteria<Pair<Integer, String>> {

    private String searchText;

    public CriterionContainsString(String searchText) {
        this.searchText = searchText;
    }

    public String getSearchString(){
        return searchText;
    }
    
    @Override
    public List<Pair<Integer, String>> meetCriteria(List<Pair<Integer, String>> entities) {
        List<Pair<Integer, String>> list = new LinkedList<>();
        for (Pair<Integer, String> pair : entities) {
            if (pair.second.contains(searchText)) {
                list.add(pair);
            }
        }
        return list;
    }

}
