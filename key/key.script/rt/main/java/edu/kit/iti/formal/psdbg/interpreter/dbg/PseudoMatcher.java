package edu.kit.iti.formal.psdbg.interpreter.dbg;

import edu.kit.iti.formal.psdbg.interpreter.MatcherApi;
import edu.kit.iti.formal.psdbg.interpreter.data.GoalNode;
import edu.kit.iti.formal.psdbg.interpreter.data.VariableAssignment;
import edu.kit.iti.formal.psdbg.parser.data.Value;
import edu.kit.iti.formal.psdbg.parser.types.SimpleType;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class PseudoMatcher implements MatcherApi<String> {
    private static Set<String> getNamedGroupCandidates(String regex) {
        Set<String> namedGroups = new TreeSet<String>();
        Matcher m = Pattern.compile("\\(\\?<([a-zA-Z][a-zA-Z0-9]*)>").matcher(regex);
        while (m.find()) {
            namedGroups.add(m.group(1));
        }
        return namedGroups;
    }

    @Override
    public List<VariableAssignment> matchLabel(GoalNode<String> currentState, String label) {
        Pattern p = Pattern.compile(label, Pattern.CASE_INSENSITIVE);
        Matcher m = p.matcher(currentState.getData());
        return m.matches()
                ? Collections.singletonList(new VariableAssignment())
                : Collections.emptyList();
    }

    @Override
    public List<VariableAssignment> matchSeq(GoalNode<String> currentState, String data) {
        Pattern p = Pattern.compile(data, Pattern.CASE_INSENSITIVE);
        Matcher m = p.matcher(currentState.getData());
        if (!m.matches())
            return Collections.emptyList();

        VariableAssignment va = new VariableAssignment();
        for (String groupName : getNamedGroupCandidates(data)) {
            String value = m.group(groupName);
            if (value != null) {
                va.declare(groupName, SimpleType.STRING);
                va.assign(groupName, Value.from(m.group(groupName)));
            }
        }
        return Collections.singletonList(va);
    }
}

   