package se.gu.svanefalk.tackey.constants;

import java.util.LinkedList;
import java.util.List;

public class TacletTypes {
    public static final String INTEGER = "int";

    public static List<String> getAsList() {
        final List<String> list = new LinkedList<>();
        list.add(INTEGER);
        return list;
    }
}