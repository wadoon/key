package se.gu.svanefalk.tackey.constants;

import java.util.LinkedList;
import java.util.List;

public class TacletComparators {
    public static final String LESS_THAN = "lt";
    public static final String GREATER_THAN = "gt";
    public static final String LESS_OR_EQUALS = "leq";
    public static final String GREATER_OR_EQUALS = "geq";

    public static List<String> getAsList() {
        final List<String> list = new LinkedList<>();
        list.add(LESS_THAN);
        list.add(LESS_OR_EQUALS);
        list.add(GREATER_THAN);
        list.add(GREATER_OR_EQUALS);
        return list;
    }
}