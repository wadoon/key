package recoder.service;

import recoder.ModelElement;
import recoder.convenience.Format;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.util.Debug;

public class DetachChange extends TreeChange {
    private final NonTerminalProgramElement parent;

    private int position;

    private AttachChange replacement;

    DetachChange(ProgramElement root, NonTerminalProgramElement parent, int position) {
        super(root);
        this.parent = parent;
        this.position = position;
        if (position < 0)
            throw new IllegalChangeReportException("Illegal position code in " + toString());
    }

    DetachChange(ProgramElement root, AttachChange replacement) {
        super(root);
        Debug.assertNonnull(replacement);
        this.replacement = replacement;
        ProgramElement rep = replacement.getChangeRoot();
        this.parent = rep.getASTParent();
        if (this.parent != null) {
            this.position = this.parent.getChildPositionCode(rep);
            if (this.position < 0)
                throw new IllegalChangeReportException("Illegal position code in " + replacement.toString());
        }
    }

    public final NonTerminalProgramElement getChangeRootParent() {
        return this.parent;
    }

    public final int getChangePositionCode() {
        return this.position;
    }

    public final AttachChange getReplacement() {
        return this.replacement;
    }

    final void setReplacement(AttachChange ac) {
        this.replacement = ac;
    }

    public String toString() {
        StringBuffer buf = new StringBuffer();
        if (isMinor())
            buf.append("Minor ");
        buf.append("Detached: ");
        if (getChangeRoot() instanceof recoder.java.CompilationUnit) {
            buf.append(Format.toString("%c %u", getChangeRoot()));
        } else {
            buf.append(Format.toString("%c %n", getChangeRoot()));
            buf.append(Format.toString(" from %c %n in %u @%p", getChangeRootParent()));
        }
        return buf.toString();
    }
}
