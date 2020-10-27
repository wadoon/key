package recoder.java.declaration;

import recoder.java.NonTerminalProgramElement;

public interface TypeDeclarationContainer extends NonTerminalProgramElement {
    int getTypeDeclarationCount();

    TypeDeclaration getTypeDeclarationAt(int paramInt);
}
