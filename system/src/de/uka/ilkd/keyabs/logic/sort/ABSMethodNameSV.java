package de.uka.ilkd.keyabs.logic.sort;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.IProgramSVSort;
import de.uka.ilkd.keyabs.abs.ABSServices;

public class ABSMethodNameSV extends ABSProgramSVSort {

    private final ProgramElementName methodName;

    public ABSMethodNameSV() {
	super(new Name("MethodName"));
	this.methodName = null;
    }

    public ABSMethodNameSV(ProgramElementName name) {
	super(new Name("MethodName"));
	this.methodName = name;
    }

    @Override
    public boolean canStandFor(ProgramElement check, ExecutionContext ec,
	    ABSServices services) {
	if (check instanceof MethodName) {
	    return methodName == null ? true : check.equals(methodName);
	}
	return false;
    }

    public IProgramSVSort<ABSServices> createInstance(String parameter) {
	return new ABSMethodNameSV(new ProgramElementName(parameter));
    }
    
    public String declarationString() {
	return name().toString();
    }

}
