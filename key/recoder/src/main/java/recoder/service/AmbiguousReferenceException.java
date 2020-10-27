package recoder.service;

import recoder.ModelException;
import recoder.abstraction.ProgramModelElement;
import recoder.java.Reference;

import java.util.ArrayList;
import java.util.List;

public class AmbiguousReferenceException extends ModelException {
    private static final long serialVersionUID = 1106306098306634107L;

    private final Reference reference;

    private final List<? extends ProgramModelElement> choices;

    public AmbiguousReferenceException(Reference r, List<? extends ProgramModelElement> choices) {
        this.reference = r;
        this.choices = choices;
    }

    public AmbiguousReferenceException(Reference r, ProgramModelElement choice1, ProgramModelElement choice2) {
        this.reference = r;
        List<ProgramModelElement> list = new ArrayList<ProgramModelElement>(2);
        list.add(choice1);
        list.add(choice2);
        this.choices = list;
    }

    public AmbiguousReferenceException(String s, Reference r, List<? extends ProgramModelElement> choices) {
        super(s);
        this.reference = r;
        this.choices = choices;
    }

    public AmbiguousReferenceException(String s, Reference r, ProgramModelElement choice1, ProgramModelElement choice2) {
        super(s);
        this.reference = r;
        List<ProgramModelElement> list = new ArrayList<ProgramModelElement>(2);
        list.add(choice1);
        list.add(choice2);
        this.choices = list;
    }

    public Reference getAmbiguousReference() {
        return this.reference;
    }

    public List<? extends ProgramModelElement> getPossibleResolutions() {
        return this.choices;
    }
}
