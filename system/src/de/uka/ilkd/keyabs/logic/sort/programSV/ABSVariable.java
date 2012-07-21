package de.uka.ilkd.keyabs.logic.sort.programSV;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.logic.sort.ABSProgramSVSort;

public class ABSVariable extends ABSProgramSVSort {

    public ABSVariable() {
        super(new Name("Variable"));
    }

    @Override
    public boolean canStandFor(Term t) {
        return t.op() instanceof IProgramVariable;
    }

    @Override
    public boolean canStandFor(ProgramElement check, ExecutionContext ec,
            ABSServices services) {
        return check instanceof IProgramVariable;
    }
}
