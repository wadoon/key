package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;

public class ModelBasedSecSpecImpl implements ModelBasedSecSpec {
    protected KeYJavaType forClass;

    
    public ModelBasedSecSpecImpl(KeYJavaType forClass) {
            this.forClass = forClass;
    }

    @Override
    public String getName() {
        // TODO stub
        return "NAME_dummy";
    }

    @Override
    public String getDisplayName() {
        // TODO stub
        return "DISPLAYNAME_dummy";
    }

    @Override
    public VisibilityModifier getVisibility() {
     // TODO stub
        System.out.println("asked for visibility");
        return null;
    }

    @Override
    public KeYJavaType getKJT() {
     return forClass;
    }

}
