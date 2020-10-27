package recoder.java.declaration;

import recoder.java.Declaration;

public interface MemberDeclaration extends Declaration {
    TypeDeclaration getMemberParent();

    void setMemberParent(TypeDeclaration paramTypeDeclaration);

    boolean isPrivate();

    boolean isProtected();

    boolean isPublic();

    boolean isStatic();

    boolean isStrictFp();
}
