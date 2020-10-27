package recoder.bytecode;

import recoder.ModelException;
import recoder.abstraction.ProgramModelElement;
import recoder.service.ProgramModelInfo;

public abstract class ByteCodeElement implements ProgramModelElement {
    protected int accessFlags;

    protected String name;

    protected ProgramModelInfo service;

    public ByteCodeElement() {
    }

    public ByteCodeElement(int accessFlags) {
        this.accessFlags = accessFlags;
    }

    public ByteCodeElement(int accessFlags, String name) {
        setName(name);
        this.accessFlags = accessFlags;
    }

    public final String getName() {
        return this.name;
    }

    final void setName(String name) {
        this.name = name.intern();
    }

    public abstract String getTypeName();

    public final int getAccessFlags() {
        return this.accessFlags;
    }

    public void setAccessFlags(int accessFlags) {
        this.accessFlags = accessFlags;
    }

    public boolean isAbstract() {
        return ((this.accessFlags & 0x400) != 0);
    }

    public boolean isFinal() {
        return ((this.accessFlags & 0x10) != 0);
    }

    public boolean isStatic() {
        return ((this.accessFlags & 0x8) != 0);
    }

    public boolean isPrivate() {
        return ((this.accessFlags & 0x2) != 0);
    }

    public boolean isProtected() {
        return ((this.accessFlags & 0x4) != 0);
    }

    public boolean isPublic() {
        return ((this.accessFlags & 0x1) != 0);
    }

    public boolean isStrictFp() {
        return ((this.accessFlags & 0x800) != 0);
    }

    public boolean isNative() {
        return ((this.accessFlags & 0x100) != 0);
    }

    public boolean isSynchronized() {
        return ((this.accessFlags & 0x20) != 0);
    }

    public ProgramModelInfo getProgramModelInfo() {
        return this.service;
    }

    public void setProgramModelInfo(ProgramModelInfo service) {
        this.service = service;
    }

    public void validate() throws ModelException {
    }
}
