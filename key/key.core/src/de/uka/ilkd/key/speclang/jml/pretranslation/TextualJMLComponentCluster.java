package de.uka.ilkd.key.speclang.jml.pretranslation;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.speclang.PositionedString;

/**
 * A JML model-based security (information flow) specification in textual form.
 */
public class TextualJMLComponentCluster extends TextualJMLConstruct {
    
    private final PositionedString spec;

    public TextualJMLComponentCluster(ImmutableList<String> mods, PositionedString spec) {
        super(mods);
        assert spec != null;
        this.spec = spec;
        setPosition(spec);
    }
    
    public PositionedString getSpec() {
        return spec;
    }
    
    @Override
    public String toString() {
        return spec.toString();
    }
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof TextualJMLComponentCluster)) {
            return false;
        }
        TextualJMLComponentCluster other = (TextualJMLComponentCluster) o;
        return mods.equals(other.mods) && spec.equals(other.spec);
    }
    
    @Override
    public int hashCode() {
        return mods.hashCode() + spec.hashCode();
    }

}
