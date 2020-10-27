package recoder.abstraction;

import java.util.List;

public class ImplicitEnumValues extends ImplicitEnumMethod {
    public ImplicitEnumValues(ClassType ownerClass) {
        super(ownerClass);
    }

    public String getName() {
        return "values";
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }
}
