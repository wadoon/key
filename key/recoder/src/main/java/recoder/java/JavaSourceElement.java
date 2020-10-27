package recoder.java;

import recoder.ProgramFactory;

import java.io.Serializable;

public abstract class JavaSourceElement implements SourceElement, Cloneable, Serializable {
    protected static JavaProgramFactory factory = JavaProgramFactory.getInstance();

    private long positionBits = -1L;

    public JavaSourceElement() {
    }

    protected JavaSourceElement(JavaSourceElement proto) {
        if (proto == null)
            throw new NullPointerException("Cannot create something from a null prototype.");
        this.positionBits = proto.positionBits;
    }

    public SourceElement getFirstElement() {
        return this;
    }

    public SourceElement getLastElement() {
        return this;
    }

    public final SourceElement.Position getStartPosition() {
        int lc = (int) (this.positionBits >> 40L) & 0xFFFFFF;
        if (lc == 16777215)
            return SourceElement.Position.UNDEFINED;
        return new SourceElement.Position(lc >> 8, lc & 0xFF);
    }

    public final void setStartPosition(SourceElement.Position p) {
        if (p == SourceElement.Position.UNDEFINED) {
            this.positionBits |= 0xFFFFFF0000000000L;
        } else {
            int lc = Math.min(p.getLine(), 65534) << 8 | Math.min(p.getColumn(), 255);
            this.positionBits &= 0xFFFFFFFFFFL;
            this.positionBits |= lc << 40L;
        }
    }

    public final SourceElement.Position getEndPosition() {
        int lc = (int) (this.positionBits >> 16L) & 0xFFFFFF;
        if (lc == 16777215)
            return SourceElement.Position.UNDEFINED;
        return new SourceElement.Position(lc >> 8, lc & 0xFF);
    }

    public final void setEndPosition(SourceElement.Position p) {
        if (p == SourceElement.Position.UNDEFINED) {
            this.positionBits |= 0xFFFFFF0000L;
        } else {
            int lc = Math.min(p.getLine(), 65534) << 8 | Math.min(p.getColumn(), 255);
            this.positionBits &= 0xFFFFFF000000FFFFL;
            this.positionBits |= lc << 16L;
        }
    }

    public final SourceElement.Position getRelativePosition() {
        int lc = (int) this.positionBits & 0xFFFF;
        if (lc == 65535)
            return SourceElement.Position.UNDEFINED;
        return new SourceElement.Position(lc >> 8, lc & 0xFF);
    }

    public final void setRelativePosition(SourceElement.Position p) {
        if (p == SourceElement.Position.UNDEFINED) {
            this.positionBits |= 0xFFFFL;
        } else {
            int lc = Math.min(p.getLine(), 254) << 8 | Math.min(p.getColumn(), 255);
            this.positionBits &= 0xFFFFFFFFFFFF0000L;
            this.positionBits |= lc;
        }
    }

    public final ProgramFactory getFactory() {
        return factory;
    }

    public String toSource() {
        return factory.toSource(this);
    }
}
