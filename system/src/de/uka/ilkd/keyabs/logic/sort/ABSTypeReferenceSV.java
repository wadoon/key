package de.uka.ilkd.keyabs.logic.sort;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.IProgramSVSort;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.ABSTypeReference;

public class ABSTypeReferenceSV extends ABSProgramSVSort implements
        IProgramSVSort<ABSServices> {

    public ABSTypeReferenceSV() {
        super(new Name("ABSTypeRef"));
    }

    @Override
    public boolean canStandFor(ProgramElement check, ExecutionContext ec,
            ABSServices services) {
        return check instanceof ABSTypeReference;
    }

}
