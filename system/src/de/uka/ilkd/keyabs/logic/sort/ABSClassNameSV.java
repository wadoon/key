package de.uka.ilkd.keyabs.logic.sort;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.IProgramSVSort;
import de.uka.ilkd.keyabs.abs.ABSServices;

public class ABSClassNameSV extends ABSProgramSVSort {

    private final ProgramElementName className;

    public ABSClassNameSV() {
	super(new Name("ClassName"));
	this.className = null;
    }

    public ABSClassNameSV(ProgramElementName name) {
	super(new Name("ClassName"));
	this.className = name;
    }

    @Override
    public boolean canStandFor(ProgramElement check, ExecutionContext ec,
	    ABSServices services) {
	if (check instanceof ProgramElementName && services.getJavaInfo().isClass((ProgramElementName) check)) {
	    return className == null ? true : check.equals(className);
	}
	return false;
    }

    public IProgramSVSort<ABSServices> createInstance(String parameter) {
	return new ABSClassNameSV(new ProgramElementName(parameter));
    }
    
    public String declarationString() {
	return name().toString();
    }

}
