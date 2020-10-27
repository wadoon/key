package recoder.service;

import recoder.ModelException;
import recoder.abstraction.ProgramModelElement;
import recoder.java.Declaration;

public class AmbiguousDeclarationException extends ModelException {
    private static final long serialVersionUID = -412059506748522072L;

    private Declaration declaration;

    private ProgramModelElement conflictingElement;

    public AmbiguousDeclarationException() {
    }

    public AmbiguousDeclarationException(Declaration declaration, ProgramModelElement conflictingElement) {
        this.declaration = declaration;
        this.conflictingElement = conflictingElement;
    }

    public AmbiguousDeclarationException(String s, Declaration declaration, ProgramModelElement conflictingElement) {
        super(s);
        this.declaration = declaration;
        this.conflictingElement = conflictingElement;
    }

    public Declaration getAmbiguousDeclaration() {
        return this.declaration;
    }

    public ProgramModelElement getConflictingElement() {
        return this.conflictingElement;
    }
}
