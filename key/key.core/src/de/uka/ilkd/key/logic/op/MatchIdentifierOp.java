package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Operator representing a MatchIdentifier '?' respectively '?X'
 */
public class MatchIdentifierOp extends AbstractSV implements QuantifiableVariable {


    protected MatchIdentifierOp(Name name, Sort sort, boolean isRigid, boolean isStrict) {
        super(name, sort, isRigid, isStrict);
    }

    @Override
    public String proofToString() {
        return null;
    }
}
