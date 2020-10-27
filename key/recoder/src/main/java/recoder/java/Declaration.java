package recoder.java;

import recoder.java.declaration.DeclarationSpecifier;
import recoder.list.generic.ASTList;

public interface Declaration extends NonTerminalProgramElement {
    ASTList<DeclarationSpecifier> getDeclarationSpecifiers();

    void setDeclarationSpecifiers(ASTList<DeclarationSpecifier> paramASTList);
}
