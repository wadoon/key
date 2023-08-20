package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;

import org.key_project.util.collection.ImmutableList;

/**
 * @param trigger trigger related information
 */
public record Trigger(SchemaVariable triggerVar, Term trigger, ImmutableList<Term> avoidConditions) {

    public Trigger {
        assert triggerVar != null;
        assert trigger != null;
        assert avoidConditions != null;

    }

    public Term getTerm() {
        return trigger;
    }

    public boolean hasAvoidConditions() {
        return !avoidConditions.isEmpty();
    }

}
