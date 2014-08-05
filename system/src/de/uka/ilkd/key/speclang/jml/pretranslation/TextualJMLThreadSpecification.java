package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.speclang.PositionedString;

import static de.uka.ilkd.key.util.MiscTools.equalsOrNull;

public final class TextualJMLThreadSpecification extends TextualJMLConstruct {

    private ImmutableList<PositionedString> pres = ImmutableSLList.nil();
    private ImmutableList<PositionedString> relies = ImmutableSLList.nil();
    private ImmutableList<PositionedString> guarantees = ImmutableSLList.nil();
    private PositionedString notAssigned;
    private PositionedString assignable;

    public TextualJMLThreadSpecification(ImmutableList<String> mods) {
        super(ImmutableSLList.<String>nil()); // modifiers are currently ignored
    }
    
    // Implementation note: append() more expensive than prepend(), but preserves original order

    void addPre (PositionedString newPre) {
        pres = relies.append(newPre);
        setPosition(newPre);
    }
    
    void addRely (PositionedString newRely) {
        relies = relies.append(newRely);
        setPosition(newRely);
    }
    
    void addGuarantee(PositionedString newGuarantee) {
        guarantees = guarantees.append(newGuarantee);
        setPosition(newGuarantee);
    }
    
    void setNotAssigned(PositionedString newNotAssigned) {
        notAssigned = newNotAssigned;
        setPosition(newNotAssigned);
    }
    
    void setAssignable(PositionedString newAssignable) {
        assignable = newAssignable;
        setPosition(newAssignable);
    }
    
    public ImmutableList<PositionedString> getPres() {
        return pres;
    }

    
    public ImmutableList<PositionedString> getRelies() {
        return relies;
    }

    
    public ImmutableList<PositionedString> getGuarantees() {
        return guarantees;
    }

    
    public PositionedString getNotAssigned() {
        return notAssigned;
    }

    
    public PositionedString getAssignable() {
        return assignable;
    }
    
    @Override
    public String toString() {
        final StringBuffer sb = new StringBuffer();
        sb.append("concurrent_behavior\n");
        for (PositionedString pre: pres) {
            sb.append("requires ");
            sb.append(pre.toString());
            sb.append(';');
            sb.append('\n');
        }
        for (PositionedString rely: relies) {
            sb.append("relies_on ");
            sb.append(rely.toString());
            sb.append(';');
            sb.append('\n');
        }
        for (PositionedString guar: guarantees) {
            sb.append("guarantees ");
            sb.append(guar.toString());
            sb.append(';');
            sb.append('\n');
        }
        if (notAssigned != null) {
            sb.append("not_assigned ");
            sb.append(notAssigned);
            sb.append(';');
            sb.append('\n');
        }
        if (assignable != null) {
            sb.append("assignable ");
            sb.append(assignable);
            sb.append(';');
            sb.append('\n');
        }
        return sb.toString();
    }
    
    @Override
    public boolean equals (Object o) {
        if (o instanceof TextualJMLThreadSpecification) {
            final TextualJMLThreadSpecification t = (TextualJMLThreadSpecification) o;
            return t.pres.equals(this.pres) && t.relies.equals(this.relies)
                            && t.guarantees.equals(guarantees)
                            && equalsOrNull(t.notAssigned,notAssigned)
                            && equalsOrNull(t.assignable,assignable);
        } else return false;
    }
}
