package recoder.java.reference;

import recoder.java.ProgramElement;

public interface ReferencePrefix extends ProgramElement {
    ReferenceSuffix getReferenceSuffix();

    void setReferenceSuffix(ReferenceSuffix paramReferenceSuffix);
}
