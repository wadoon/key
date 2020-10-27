package recoder.java;

import recoder.ModelException;

public interface NonTerminalProgramElement extends ProgramElement {
    int getChildCount();

    ProgramElement getChildAt(int paramInt);

    int getIndexOfChild(ProgramElement paramProgramElement);

    int getChildPositionCode(ProgramElement paramProgramElement);

    int getIndexOfChild(int paramInt);

    int getRoleOfChild(int paramInt);

    void makeParentRoleValid();

    void makeAllParentRolesValid();

    void validateAll() throws ModelException;

    boolean replaceChild(ProgramElement paramProgramElement1, ProgramElement paramProgramElement2);
}
