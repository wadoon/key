package recoder.kit;

import recoder.java.declaration.MemberDeclaration;

public class IllegalInterfaceMember extends Conflict {
    private static final long serialVersionUID = -1632587249722947504L;

    private final MemberDeclaration member;

    public IllegalInterfaceMember(MemberDeclaration member) {
        this.member = member;
    }

    public MemberDeclaration getMember() {
        return this.member;
    }
}
