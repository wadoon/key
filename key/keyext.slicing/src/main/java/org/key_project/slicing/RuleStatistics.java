package org.key_project.slicing;

import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Quadruple;
import de.uka.ilkd.key.util.Triple;

import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class RuleStatistics {
    private final Map<String, Triple<Integer, Integer, Integer>> map = new HashMap<>();
    private final Map<String, Boolean> ruleBranched = new HashMap<>();

    public void addApplication(Rule rule, boolean branches) {
        var name = rule.displayName();
        ruleBranched.put(name, branches);
        var entry = map.computeIfAbsent(name, it -> new Triple<>(0, 0, 0));
        map.put(name, new Triple<>(entry.first + 1, entry.second, entry.third));
    }

    public void addUselessApplication(Rule rule, boolean branches) {
        var name = rule.displayName();
        ruleBranched.put(name, branches);
        var entry = map.computeIfAbsent(name, it -> new Triple<>(0, 0, 0));
        map.put(name, new Triple<>(entry.first + 1, entry.second + 1, entry.third));
    }

    public void addInitialUselessApplication(Rule rule, boolean branches) {
        var name = rule.displayName();
        ruleBranched.put(name, branches);
        var entry = map.computeIfAbsent(name, it -> new Triple<>(0, 0, 0));
        map.put(name, new Triple<>(entry.first + 1, entry.second + 1, entry.third + 1));
    }

    public List<Quadruple<String, Integer, Integer, Integer>> sortBy(Comparator<Quadruple<String, Integer, Integer, Integer>> comparator) {
        return map.entrySet().stream()
                .map(entry -> new Quadruple<>(entry.getKey(), entry.getValue().first, entry.getValue().second, entry.getValue().third))
                .sorted(comparator)
                .collect(Collectors.toList());
    }

    public boolean branches(String rule) {
        return ruleBranched.get(rule);
    }
}
