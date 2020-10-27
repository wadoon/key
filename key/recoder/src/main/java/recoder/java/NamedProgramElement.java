package recoder.java;

import recoder.NamedModelElement;

public interface NamedProgramElement extends NamedModelElement, NonTerminalProgramElement {
    Identifier getIdentifier();

    void setIdentifier(Identifier paramIdentifier);
}
