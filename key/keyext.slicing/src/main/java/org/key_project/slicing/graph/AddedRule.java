package org.key_project.slicing.graph;

import java.util.Objects;

public class AddedRule implements GraphNode {
    public final String name;

    public AddedRule(String name) {
        this.name = name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        AddedRule addedRule = (AddedRule) o;
        return Objects.equals(name, addedRule.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }

    public String toString(boolean abbreviated) {
        return "added rule " + name;
    }
}
