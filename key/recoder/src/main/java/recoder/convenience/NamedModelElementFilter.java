package recoder.convenience;

import recoder.ModelElement;
import recoder.NamedModelElement;

public class NamedModelElementFilter implements ModelElementFilter {
    private final Class type;

    private final String name;

    public NamedModelElementFilter(String name) {
        this.type = NamedModelElement.class;
        this.name = name;
    }

    public NamedModelElementFilter(Class<?> type, String name) {
        if (!NamedModelElement.class.isAssignableFrom(type))
            throw new IllegalArgumentException("Given type is no subtype of NamedModelElement");
        this.type = type;
        this.name = name;
    }

    public boolean accept(ModelElement e) {
        return (this.type.isInstance(e) && this.name.equals(((NamedModelElement) e).getName()));
    }
}
