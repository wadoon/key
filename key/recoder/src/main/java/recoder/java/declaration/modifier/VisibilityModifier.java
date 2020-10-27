package recoder.java.declaration.modifier;

import recoder.java.declaration.Modifier;

public abstract class VisibilityModifier extends Modifier {
    public VisibilityModifier() {
    }

    protected VisibilityModifier(VisibilityModifier proto) {
        super(proto);
    }
}
