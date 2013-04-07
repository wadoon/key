package de.uka.ilkd.keyabs.logic.sort.programSV;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.IABSMethodLabel;
import de.uka.ilkd.keyabs.logic.sort.ABSProgramSVSort;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 06.04.13
 * Time: 23:04
 * To change this template use File | Settings | File Templates.
 */
public class ABSMethodLabelSV extends ABSProgramSVSort {


    public ABSMethodLabelSV() {
        super(new Name("MethodLabel"));
    }

    @Override
    public boolean canStandFor(ProgramElement check, ExecutionContext ec, ABSServices services) {
        return check instanceof IABSMethodLabel;
    }
}
