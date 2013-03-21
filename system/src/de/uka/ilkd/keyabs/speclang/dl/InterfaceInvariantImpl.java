package de.uka.ilkd.keyabs.speclang.dl;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ParsableVariable;

/**
 * Represents an in interface invariant specification
 */
public class InterfaceInvariantImpl implements InterfaceInvariant {

    private final String name;
    private final String displayName;
    private final KeYJavaType kjt;
    private final Term inv;


    public InterfaceInvariantImpl(String name,
                                  String displayName,
                                  KeYJavaType kjt,
                                  Term inv) {
        this.name = name;
        this.displayName = displayName;
        this.kjt = kjt;
        this.inv = inv;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public String getDisplayName() {
        return displayName;
    }

    @Override
    public VisibilityModifier getVisibility() {
        return null;
    }

    @Override
    public KeYJavaType getKJT() {
        return kjt;
    }

    public Term getOriginalInvariant() {
        return inv;
    }

    public Term getInvariant() {
        return inv;
    }



}
