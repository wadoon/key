package org.key_project.slicing.graph;

import java.util.Objects;

/**
 * Graph node that represents a rule added by some rule application.
 *
 * @author Arne Keller
 */
public class AddedRule implements GraphNode {
    /**
     * The name of the added rule.
     */
    public final String name;

    public AddedRule(String name) {
        this.name = name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        AddedRule addedRule = (AddedRule) o;
        return Objects.equals(name, addedRule.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }

    @Override
    public String toString(boolean abbreviated) {
        return "added rule " + name;
    }
}
