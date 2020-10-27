package recoder.java.statement;

import recoder.java.Identifier;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.reference.NameReference;

public abstract class LabelJumpStatement extends JumpStatement implements NameReference {
    protected Identifier name;

    public LabelJumpStatement() {
    }

    public LabelJumpStatement(Identifier label) {
        setIdentifier(label);
    }

    protected LabelJumpStatement(LabelJumpStatement proto) {
        super(proto);
        if (proto.name != null)
            this.name = proto.name.deepClone();
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (this.name != null)
            this.name.setParent(this);
    }

    public final String getName() {
        return (this.name == null) ? null : this.name.getText();
    }

    public Identifier getIdentifier() {
        return this.name;
    }

    public void setIdentifier(Identifier id) {
        this.name = id;
    }

    public int getChildCount() {
        return (this.name != null) ? 1 : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (this.name != null &&
                index == 0)
            return this.name;
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        if (this.name == child)
            return 0;
        return -1;
    }

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null)
            throw new NullPointerException();
        if (this.name == p) {
            Identifier r = (Identifier) q;
            this.name = r;
            if (r != null)
                r.setParent(this);
            return true;
        }
        return false;
    }
}
