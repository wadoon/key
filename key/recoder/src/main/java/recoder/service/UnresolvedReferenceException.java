package recoder.service;

import recoder.ModelException;
import recoder.java.ProgramElement;

public class UnresolvedReferenceException extends ModelException {
    private static final long serialVersionUID = 4926742139318960014L;

    private final ProgramElement programElement;

    public UnresolvedReferenceException(ProgramElement r) {
        this.programElement = r;
    }

    public UnresolvedReferenceException(String s, ProgramElement r) {
        super(s);
        this.programElement = r;
    }

    public ProgramElement getUnresolvedReference() {
        return this.programElement;
    }
}
