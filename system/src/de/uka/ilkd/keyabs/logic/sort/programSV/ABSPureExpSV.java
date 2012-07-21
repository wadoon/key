package de.uka.ilkd.keyabs.logic.sort.programSV;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.IABSPureExpression;
import de.uka.ilkd.keyabs.logic.sort.ABSProgramSVSort;

public class ABSPureExpSV extends ABSProgramSVSort {

    public ABSPureExpSV() {
        super(new Name("PureExp"));
    }

    @Override
    public boolean canStandFor(ProgramElement check, ExecutionContext ec,
            ABSServices services) {
        return check instanceof IABSPureExpression;
    }
    
}
