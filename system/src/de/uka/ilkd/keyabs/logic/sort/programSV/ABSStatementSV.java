package de.uka.ilkd.keyabs.logic.sort.programSV;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.logic.sort.ABSProgramSVSort;

public class ABSStatementSV extends ABSProgramSVSort {

    public ABSStatementSV() {
        super(new Name("Statement"));
    }

    @Override
    public boolean canStandFor(ProgramElement check, ExecutionContext ec,
            ABSServices services) {
        return check instanceof Statement;
    }

}
