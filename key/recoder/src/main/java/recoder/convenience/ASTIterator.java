package recoder.convenience;

import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

public class ASTIterator {
    public static final int ENTER_NONE = 0;

    public static final int ENTER_SOME = 1;

    public static final int ENTER_ALL = 2;

    ASTIteratorListener listener = null;

    public ASTIterator() {
    }

    public ASTIterator(ASTIteratorListener l) {
        setListener(l);
    }

    public void setListener(ASTIteratorListener l) {
        this.listener = l;
    }

    public void iterate(ProgramElement pe) {
        if (this.listener != null) {
            recurse(pe);
        } else {
            simpleRecurse(pe);
        }
    }

    protected void recurse(ProgramElement pe) {
        if (pe != null) {
            this.listener.enteringNode(this, pe);
            if (pe instanceof NonTerminalProgramElement) {
                int childCount, i;
                NonTerminalProgramElement ntpe = (NonTerminalProgramElement) pe;
                switch (this.listener.enterChildren(this, ntpe)) {
                    case 1:
                        childCount = ntpe.getChildCount();
                        for (i = 0; i < childCount; i++) {
                            ProgramElement child = ntpe.getChildAt(i);
                            if (this.listener.enterChildNode(this, ntpe, child)) {
                                recurse(child);
                                this.listener.returnedFromChildNode(this, ntpe, child);
                            }
                        }
                        break;
                    case 2:
                        childCount = ntpe.getChildCount();
                        for (i = 0; i < childCount; i++) {
                            ProgramElement child = ntpe.getChildAt(i);
                            recurse(child);
                        }
                        break;
                }
            }
            this.listener.leavingNode(this, pe);
        }
    }

    protected void simpleRecurse(ProgramElement pe) {
        if (pe instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement ntpe = (NonTerminalProgramElement) pe;
            int childCount = ntpe.getChildCount();
            for (int i = 0; i < childCount; i++) {
                ProgramElement child = ntpe.getChildAt(i);
                simpleRecurse(child);
            }
        }
    }
}
