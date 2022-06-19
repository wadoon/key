package org.key_project.slicing.graph;

import org.key_project.util.collection.ImmutableSLList;

import java.util.Objects;

/**
 * Graph node that represents a rule added by some rule application.
 *
 * @author Arne Keller
 */
public class AddedRule extends GraphNode {
    /**
     * The name of the added rule.
     */
    public final String name;

    public AddedRule(String name) {
        super(ImmutableSLList.nil()); // TODO
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
    public String toString(boolean abbreviated, boolean omitBranch) {
        return "added rule " + name;
    }
}
