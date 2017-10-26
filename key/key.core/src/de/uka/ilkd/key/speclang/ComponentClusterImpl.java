package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.util.Lowlist;
import de.uka.ilkd.key.util.VisibilityCondition;

public class ComponentClusterImpl extends AbstractDependencyClusterSpec implements ComponentCluster {
    protected KeYJavaType forClass;
    
    private final String label;
    private final ImmutableList<Lowlist> lowIn;
    private final ImmutableList<Lowlist> lowOut;
    private final ImmutableList<Term> lowState;   
    private final ImmutableList<VisibilityCondition> visible;

    
    public ComponentClusterImpl(KeYJavaType forClass, ImmutableList<Lowlist> lowIn, ImmutableList<Lowlist> lowOut, 
            ImmutableList<Term> lowState, ImmutableList<VisibilityCondition> visible, String label, Services services) {
        super(label, services);
            this.forClass = forClass;
            
            this.lowIn = lowIn;
            this.lowOut = lowOut;
            this.lowState = lowState;
            this.visible = visible;
            this.label = label;
    }
    
    public ImmutableList<Lowlist> getLowOut() {
        return lowOut;
    }

    public ImmutableList<Lowlist> getLowIn() {
        return lowIn;
    }

    public ImmutableList<Term> getLowState() {
        return lowState;
    }

    public ImmutableList<VisibilityCondition> getVisible() {
        return visible;
    }
    
    public String getLabel() {
        return label;
    }
    
    
    @Override
    public String toString() {
        return  "Label: " + label+ "\n" +
                "LowIn: " + lowIn + "\n" +
                "LowOut: " + lowOut + "\n" +
                "lowState: " + lowState + "\n" +
                "Visible: " + visible;
    }

    @Override
    public String getName() {
        // TODO JK stub
        return "NAME_dummy";
    }

    @Override
    public String getDisplayName() {
        // TODO JK stub
        return "DISPLAYNAME_dummy";
    }

    @Override
    public VisibilityModifier getVisibility() {
     // TODO JK stub
        System.out.println("asked for visibility");
        return null;
    }

    @Override
    public KeYJavaType getKJT() {
     return forClass;
    }

    @Override
    public void registerPredicatesAndTaclets() {
        // TODO Auto-generated method stub
        
    }


}
