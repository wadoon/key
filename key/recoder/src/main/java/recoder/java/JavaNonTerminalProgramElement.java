package recoder.java;

import recoder.ModelException;
import recoder.convenience.TreeWalker;

public abstract class JavaNonTerminalProgramElement extends JavaProgramElement implements NonTerminalProgramElement {
    public JavaNonTerminalProgramElement() {
    }

    protected JavaNonTerminalProgramElement(JavaProgramElement proto) {
        super(proto);
    }

    public void makeParentRoleValid() {
    }

    public void makeAllParentRolesValid() {
        TreeWalker tw = new TreeWalker(this);
        while (tw.next(NonTerminalProgramElement.class))
            ((NonTerminalProgramElement) tw.getProgramElement()).makeParentRoleValid();
    }

    public int getIndexOfChild(int positionCode) {
        return positionCode >> 4;
    }

    public int getRoleOfChild(int positionCode) {
        return positionCode & 0xF;
    }

    public int getIndexOfChild(ProgramElement child) {
        int i;
        for (i = getChildCount() - 1; i >= 0 && getChildAt(i) != child; i--) ;
        return i;
    }

    public void validateAll() throws ModelException {
        TreeWalker tw = new TreeWalker(this);
        while (tw.next())
            tw.getProgramElement().validate();
    }
}
