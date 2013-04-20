package se.gu.svanefalk.tackey.constants;

import java.util.LinkedList;
import java.util.List;

public class TacletOperators {
    public static final String MULTIPLY = "mul";
    public static final String ADD = "add";
    public static final String SUBTRACT = "sub";
    public static final String DIVIDE = "div";

    public static List<String> getAsList() {
        final List<String> list = new LinkedList<>();
        list.add(ADD);
        list.add(SUBTRACT);
        list.add(MULTIPLY);
        list.add(DIVIDE);
        return list;
    }
}
