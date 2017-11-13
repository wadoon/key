package de.uka.ilkd.key.speclang;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.dependencycluster.po.AgreeTacletFactory;
import de.uka.ilkd.key.dependencycluster.po.EventEquivalenceWithEqFactory;
import de.uka.ilkd.key.dependencycluster.po.EventEquivalenceWithIsoFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.util.Lowlist;
import de.uka.ilkd.key.util.VisibilityCondition;

public class ServiceDependencyClusterSpec extends AbstractDependencyClusterSpec {
    protected KeYJavaType forClass;

    private final ImmutableList<Lowlist> lowIn;
    private final ImmutableList<Lowlist> lowOut;
    private final ImmutableList<Term> lowState;
    private final ImmutableList<Term> newObjects;
    
    private final ImmutableList<VisibilityCondition> visible;




    public ServiceDependencyClusterSpec(KeYJavaType forClass, ImmutableList<Lowlist> lowIn, ImmutableList<Lowlist> lowOut, ImmutableList<Term> lowState, 
            ImmutableList<VisibilityCondition> visible, ImmutableList<Term> newObjects, String label, Services services) {
        super(label, services);
        this.lowIn = lowIn;
        this.lowOut = lowOut;
        this.lowState = lowState;
        this.visible = visible;
        this.newObjects = newObjects;
        
        this.forClass = forClass;
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

    public ImmutableList<Term> getNewObjects() {
        return newObjects;
    }

    public ImmutableList<VisibilityCondition> getVisible() {
        return visible;
    }

    
    
    @Override
    public String toString() {
        return  "Label: " + label+ "\n" +
                "LowIn: " + lowIn + "\n" +
                "LowOut: " + lowOut + "\n" +
                "lowState: " + lowState + "\n" +
                "Visible: " + visible + "\n" +
                "New Objects: " + newObjects;
    }


    @Override
    public ImmutableList<RewriteTaclet> getTaclets(Term self, InitConfig config) {
        Services services = config.getServices();
        EventEquivalenceWithEqFactory eqFactory = new EventEquivalenceWithEqFactory(this, self, services, getEquivEventEqPredicate(), getVisibilityPredicate(), label);
        EventEquivalenceWithIsoFactory isoFactory = new EventEquivalenceWithIsoFactory(this, services, self, getEquivEventIsoPredicate(), getVisibilityPredicate(), label);
        AgreeTacletFactory agreeFactory = new AgreeTacletFactory(getLowState(), self, services, label, getAgreePrePredicate(), getAgreePostPredicate());
        
        ImmutableList<RewriteTaclet> taclets = ImmutableSLList.<RewriteTaclet>nil();
        
        
        taclets = taclets.prepend(eqFactory.getInvisibilityTaclet());
        taclets = taclets.prepend(eqFactory.getEventEquivalenceTaclet());
        taclets = taclets.prepend(isoFactory.getEventEquivalenceTaclet());
        taclets = taclets.prepend(agreeFactory.getAgreePreTaclet());
        taclets = taclets.prepend(agreeFactory.getAgreePostTaclet());
        
        return taclets;
    }


    @Override
    public String getName() {
        return label;
    }


    @Override
    public String getDisplayName() {
        return label;
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

}
