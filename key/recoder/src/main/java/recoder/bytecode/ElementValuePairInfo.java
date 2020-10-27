package recoder.bytecode;

import recoder.abstraction.ElementValuePair;

public class ElementValuePairInfo implements ElementValuePair {
    private final String elementName;

    private final Object value;

    private final String parent;

    public ElementValuePairInfo(String elementName, Object value, String parent) {
        this.elementName = elementName;
        this.value = value;
        this.parent = parent;
    }

    public Object getValue() {
        return this.value;
    }

    public String getElementName() {
        return this.elementName;
    }

    public String getFullNameOfContainingAnnotation() {
        return this.parent;
    }

    public String toString() {
        return getElementName() + "=" + getValue();
    }
}
