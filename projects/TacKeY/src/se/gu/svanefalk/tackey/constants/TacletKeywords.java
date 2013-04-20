package se.gu.svanefalk.tackey.constants;

import java.util.LinkedList;
import java.util.List;

public final class TacletKeywords {

    public static final String ADD = "\\add";
    public static final String EXISTS = "\\exists";
    public static final String ASSUMES = "\\assumes";
    public static final String DEPENDINGON = "\\dependingOn";
    public static final String DISPLAYNAME = "\\displayname";
    public static final String ELSE = "\\else";
    public static final String ENDMODALITY = "\\endmodality";
    public static final String FIND = "\\find";
    public static final String FORMULA = "\\formula";
    public static final String FUNCTIONS = "\\functions";
    public static final String HEURISTICS = "\\heuristics";
    public static final String IF = "\\if";
    public static final String MODALITY = "\\modality";
    public static final String MODIFIES = "\\modifies";
    public static final String NEW = "\\new";
    public static final String PROGRAM = "\\program";
    public static final String PROGRAMVARIABLES = "\\programVariables";
    public static final String REPLACEWITH = "\\replacewith";
    public static final String RULES = "\\rules";
    public static final String SAMEUPDATELEVEL = "\\sameUpdateLevel";
    public static final String SCHEMAVAR = "\\schemaVar";
    public static final String SCHEMAVARIABLES = "\\schemaVariables";
    public static final String THEN = "\\then";
    public static final String VARCOND = "\\varcond";
    public static final String TERM = "\\term";
    public static final String SKOLEM_TERM = "\\skolemTerm";
    public static final String VARIABLES = "\\variables";
    public static final String NOT_FREE_IN = "\\notFreeIn";
    public static final String SUBST = "\\subst";

    public static List<String> getAsList() {
        final List<String> list = new LinkedList<>();
        list.add(TacletKeywords.FIND);
        list.add(TacletKeywords.REPLACEWITH);
        list.add(TacletKeywords.VARCOND);
        list.add(TacletKeywords.SAMEUPDATELEVEL);
        list.add(TacletKeywords.MODALITY);
        list.add(TacletKeywords.FORMULA);
        list.add(TacletKeywords.HEURISTICS);
        list.add(TacletKeywords.ADD);
        list.add(TacletKeywords.SCHEMAVAR);
        list.add(TacletKeywords.NEW);
        list.add(TacletKeywords.DEPENDINGON);
        list.add(TacletKeywords.ENDMODALITY);
        list.add(TacletKeywords.IF);
        list.add(TacletKeywords.THEN);
        list.add(TacletKeywords.ELSE);
        list.add(TacletKeywords.PROGRAM);
        list.add(TacletKeywords.RULES);
        list.add(TacletKeywords.MODIFIES);
        list.add(TacletKeywords.PROGRAMVARIABLES);
        list.add(TacletKeywords.FUNCTIONS);
        list.add(TacletKeywords.ASSUMES);
        list.add(TacletKeywords.DISPLAYNAME);
        list.add(TacletKeywords.SCHEMAVARIABLES);
        list.add(TacletKeywords.TERM);
        list.add(TacletKeywords.SKOLEM_TERM);
        list.add(TacletKeywords.VARIABLES);
        list.add(TacletKeywords.NOT_FREE_IN);
        list.add(TacletKeywords.SUBST);
        list.add(TacletKeywords.EXISTS);
        return list;
    }
}
