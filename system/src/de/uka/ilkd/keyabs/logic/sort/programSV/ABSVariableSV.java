package de.uka.ilkd.keyabs.logic.sort.programSV;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.keyabs.abs.ABSFieldReference;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.IABSLocationReference;
import de.uka.ilkd.keyabs.abs.ThisExpression;
import de.uka.ilkd.keyabs.logic.sort.ABSProgramSVSort;

public class ABSVariableSV extends ABSProgramSVSort {

    public ABSVariableSV() {
        super(new Name("Variable"));
    }

    @Override
    public boolean canStandFor(Term t) {
        return t.op() instanceof IProgramVariable;
    }

    @Override
    public boolean canStandFor(ProgramElement check, ExecutionContext ec,
            ABSServices services) {
        return check instanceof LocationVariable && !((LocationVariable)check).isMember() ;
    }
}
