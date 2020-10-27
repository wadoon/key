package recoder.abstraction;

import java.util.List;

public interface Member extends ProgramModelElement {
    boolean isFinal();

    boolean isStatic();

    boolean isPrivate();

    boolean isProtected();

    boolean isPublic();

    boolean isStrictFp();

    ClassType getContainingClassType();

    List<? extends AnnotationUse> getAnnotations();
}
