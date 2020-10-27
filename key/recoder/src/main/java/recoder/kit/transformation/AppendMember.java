package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.declaration.MemberDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.list.generic.ASTList;

public class AppendMember extends TwoPassTransformation {
    private final boolean isVisible;

    private final TypeDeclaration parent;

    private final MemberDeclaration child;

    private int insertPosition = -1;

    public AppendMember(CrossReferenceServiceConfiguration sc, boolean isVisible, MemberDeclaration child, TypeDeclaration parent) {
        super(sc);
        if (child == null || parent == null)
            throw new IllegalArgumentException("Missing declaration");
        this.isVisible = isVisible;
        this.child = child;
        this.parent = parent;
    }

    public boolean isVisible() {
        return this.isVisible;
    }

    public ProblemReport analyze() {
        ASTList<MemberDeclaration> aSTList = this.parent.getMembers();
        if (aSTList == null) {
            this.insertPosition = 0;
            return setProblemReport(NO_PROBLEM);
        }
        int lastField = -1;
        int lastInitializer = -1;
        int lastConstructor = -1;
        int lastMethod = -1;
        int lastType = -1;
        for (int i = aSTList.size() - 1; i >= 0; i--) {
            MemberDeclaration x = aSTList.get(i);
            if (x instanceof recoder.java.declaration.FieldDeclaration) {
                lastField = (lastField < 0) ? i : lastField;
            } else if (x instanceof recoder.java.declaration.ClassInitializer) {
                lastInitializer = (lastInitializer < 0) ? i : lastInitializer;
            } else if (x instanceof recoder.abstraction.Constructor) {
                lastConstructor = (lastConstructor < 0) ? i : lastConstructor;
            } else if (x instanceof recoder.abstraction.Method) {
                lastMethod = (lastMethod < 0) ? i : lastMethod;
            } else if (x instanceof recoder.abstraction.Type) {
                lastType = (lastType < 0) ? i : lastType;
            }
        }
        if (this.child instanceof recoder.java.declaration.FieldDeclaration) {
            lastInitializer = lastConstructor = lastMethod = lastType = -1;
        } else if (this.child instanceof recoder.java.declaration.ClassInitializer) {
            lastConstructor = lastMethod = lastType = -1;
        } else if (this.child instanceof recoder.java.declaration.ConstructorDeclaration) {
            lastMethod = lastType = -1;
        } else if (this.child instanceof recoder.java.declaration.MethodDeclaration) {
            lastType = -1;
        }
        if (lastType >= 0) {
            this.insertPosition = lastType + 1;
        } else if (lastMethod >= 0) {
            this.insertPosition = lastMethod + 1;
        } else if (lastConstructor >= 0) {
            this.insertPosition = lastConstructor + 1;
        } else if (lastInitializer >= 0) {
            this.insertPosition = lastInitializer + 1;
        } else if (lastField >= 0) {
            this.insertPosition = lastField + 1;
        } else {
            this.insertPosition = 0;
        }
        return setProblemReport(NO_PROBLEM);
    }

    public void transform() {
        super.transform();
        attach(this.child, this.parent, this.insertPosition);
    }
}
