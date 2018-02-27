package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Operator representing a MatchIdentifier '?' respectively '?X'
 */
public class MatchIdentifierOp extends AbstractSV implements QuantifiableVariable {
    Name name;
    Sort sort;


    protected MatchIdentifierOp(Name name, Sort sort, boolean isRigid, boolean isStrict) {
        super(name, sort, isRigid, isStrict);
        this.name = name;
        this.sort = sort;
    }

    @Override
    public String proofToString() {
        return name.toString() + ":"+sort.toString();
    }
}
