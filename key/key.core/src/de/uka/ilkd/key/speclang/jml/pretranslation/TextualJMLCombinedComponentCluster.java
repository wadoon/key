package de.uka.ilkd.key.speclang.jml.pretranslation;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.speclang.PositionedString;

/**
 * A JML component based systems information flow specification in textual form.
 */
public class TextualJMLCombinedComponentCluster extends TextualJMLConstruct {
    
    private final PositionedString spec;

    public TextualJMLCombinedComponentCluster(ImmutableList<String> mods, PositionedString spec) {
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
        if(!(o instanceof TextualJMLCombinedComponentCluster)) {
            return false;
        }
        TextualJMLCombinedComponentCluster other = (TextualJMLCombinedComponentCluster) o;
        return mods.equals(other.mods) && spec.equals(other.spec);
    }
    
    @Override
    public int hashCode() {
        return mods.hashCode() + spec.hashCode();
    }

}
