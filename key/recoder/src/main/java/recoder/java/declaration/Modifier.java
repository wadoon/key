package recoder.java.declaration;

import recoder.java.Declaration;
import recoder.java.JavaProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.TerminalProgramElement;

public abstract class Modifier extends JavaProgramElement implements DeclarationSpecifier, TerminalProgramElement {
    protected Declaration parent;

    public Modifier() {
    }

    protected Modifier(Modifier proto) {
        super(proto);
    }

    public NonTerminalProgramElement getASTParent() {
        return this.parent;
    }

    public Declaration getParentDeclaration() {
        return this.parent;
    }

    public void setParent(Declaration parent) {
        this.parent = parent;
    }
}
