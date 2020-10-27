package recoder.bytecode;

import recoder.abstraction.ClassType;
import recoder.abstraction.Member;

import java.util.List;

public abstract class MemberInfo extends ByteCodeElement implements Member {
    protected ClassFile parent;

    List<AnnotationUseInfo> annotations;

    public MemberInfo(int accessFlags, String name, ClassFile parent) {
        super(accessFlags, name);
        setParent(parent);
    }

    public ClassFile getParent() {
        return this.parent;
    }

    public void setParent(ClassFile parent) {
        this.parent = parent;
    }

    public ClassType getContainingClassType() {
        return this.service.getContainingClassType(this);
    }

    public List<AnnotationUseInfo> getAnnotations() {
        return this.annotations;
    }

    void setAnnotations(List<AnnotationUseInfo> annotations) {
        this.annotations = annotations;
    }
}
