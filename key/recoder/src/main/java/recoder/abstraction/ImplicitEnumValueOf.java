package recoder.abstraction;

import java.util.List;

public class ImplicitEnumValueOf extends ImplicitEnumMethod {
    public ImplicitEnumValueOf(ClassType ownerClass) {
        super(ownerClass);
    }

    public String getName() {
        return "valueOf";
    }

    public List<? extends TypeParameter> getTypeParameters() {
        return null;
    }
}
