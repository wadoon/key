package de.uka.ilkd.key.strategy;

import static de.uka.ilkd.key.strategy.StaticFeatureCollection.op;

import org.key_project.common.core.logic.op.Equality;
import org.key_project.common.core.logic.op.Junctor;

import de.uka.ilkd.key.strategy.termfeature.TermFeature;

class ValueTermFeature {

    public ValueTermFeature(TermFeature nullTerm) {
        equals = op(Equality.EQUALS);
        tt = op(Junctor.TRUE);
        ff = op(Junctor.FALSE);
        this.nullTerm = nullTerm;
    }

    final TermFeature equals;
    final TermFeature tt;
    final TermFeature ff;
    final TermFeature nullTerm;
}
