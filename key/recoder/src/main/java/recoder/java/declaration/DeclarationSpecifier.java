package recoder.java.declaration;

import recoder.java.Declaration;
import recoder.java.ProgramElement;

public interface DeclarationSpecifier extends ProgramElement {
    void setParent(Declaration paramDeclaration);

    Declaration getParentDeclaration();
}
