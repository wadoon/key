package recoder.java.reference;

import recoder.java.NonTerminalProgramElement;

public interface TypeReferenceContainer extends NonTerminalProgramElement {
    int getTypeReferenceCount();

    TypeReference getTypeReferenceAt(int paramInt);
}
