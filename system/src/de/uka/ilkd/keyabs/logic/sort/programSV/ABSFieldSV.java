package de.uka.ilkd.keyabs.logic.sort.programSV;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.keyabs.abs.ABSFieldReference;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.IABSFieldReference;
import de.uka.ilkd.keyabs.abs.IABSLocationReference;
import de.uka.ilkd.keyabs.logic.sort.ABSProgramSVSort;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 21.03.13
 * Time: 08:31
 * To change this template use File | Settings | File Templates.
 */
public class ABSFieldSV extends ABSProgramSVSort {

        public ABSFieldSV() {
            super(new Name("Field"));
        }

        @Override
        public boolean canStandFor(Term t) {
            return t.op() instanceof IProgramVariable;
        }

        @Override
        public boolean canStandFor(ProgramElement check, ExecutionContext ec,
                                   ABSServices services) {
            return check instanceof IABSFieldReference || (check instanceof LocationVariable &&
                    ((LocationVariable)check).isMember() );
        }
}
