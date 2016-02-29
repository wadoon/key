package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.keyabs.abs.ABSPatternVar;

public interface ProgramVisitor {

    void performActionOnProgramElementName(ProgramElementName x);

    void performActionOnProgramMethod(IProgramMethod x);

    void performActionOnSchemaVariable(SchemaVariable x);

    void performActionOnProgramVariable(ProgramVariable x);

    void performActionOnLocationVariable(LocationVariable x);

    void performActionOnProgramConstant(ProgramConstant x);
    
}