package org.key_project.slicing.util;

import de.uka.ilkd.key.util.Pair;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public final class ExecutionTime {
    private final Map<String, Long> startTimes = new LinkedHashMap<>();
    private final Map<String, Long> endTimes = new LinkedHashMap<>();

    public ExecutionTime() { }

    public void start(String activity) {
        if (startTimes.containsKey(activity)) {
            throw new IllegalStateException("tried to start already started activity!");
        }
        startTimes.put(activity, System.currentTimeMillis());
    }

    public void stop(String activity) {
        if (!startTimes.containsKey(activity)) {
            throw new IllegalStateException("tried to end unknown activity!");
        }
        endTimes.put(activity, System.currentTimeMillis());
    }

    public Stream<Pair<String, Long>> executionTimes() {
        return startTimes.entrySet().stream()
                .filter(e -> endTimes.containsKey(e.getKey()))
                .map(e -> new Pair<>(e.getKey(), endTimes.get(e.getKey()) - e.getValue()));
    }

    public Map<String, Long> executionTimesMap() {
        return startTimes.entrySet().stream()
                .filter(e -> endTimes.containsKey(e.getKey()))
                .map(e -> new Pair<>(e.getKey(), endTimes.get(e.getKey()) - e.getValue()))
                .collect(Collectors.toUnmodifiableMap(x -> x.first, x -> x.second));
    }
}
