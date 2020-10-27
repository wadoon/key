package recoder.kit;

import recoder.NamedModelElement;

public class IllegalName extends Problem {
    private static final long serialVersionUID = -6773990661739949555L;

    private final NamedModelElement element;

    public IllegalName(NamedModelElement element) {
        this.element = element;
    }

    public NamedModelElement getElement() {
        return this.element;
    }
}
