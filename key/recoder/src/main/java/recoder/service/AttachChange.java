package recoder.service;

import recoder.ModelElement;
import recoder.convenience.Format;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

public class AttachChange extends TreeChange {
    AttachChange(ProgramElement root) {
        super(root);
    }

    public final NonTerminalProgramElement getChangeRootParent() {
        return getChangeRoot().getASTParent();
    }

    public String toString() {
        StringBuffer buf = new StringBuffer();
        if (isMinor())
            buf.append("Minor ");
        buf.append("Attached: ");
        if (getChangeRoot() instanceof recoder.java.CompilationUnit) {
            buf.append(Format.toString("%c %u", getChangeRoot()));
        } else {
            buf.append(Format.toString("%c %n", getChangeRoot()));
            buf.append(Format.toString(" to %c %n in %u @%p", getChangeRootParent()));
        }
        return buf.toString();
    }
}
