package de.uka.ilkd.keyabs.init;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.pp.UIConfiguration;
import de.uka.ilkd.key.proof.DefaultGoalChooserBuilder;
import de.uka.ilkd.key.proof.DepthFirstGoalChooserBuilder;
import de.uka.ilkd.key.proof.GoalChooserBuilder;
import de.uka.ilkd.key.proof.init.AbstractInitConfig;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.pp.ABSUIConfiguration;
import de.uka.ilkd.keyabs.proof.ABSProof;
import de.uka.ilkd.keyabs.strategy.ABSDLStrategy;

public class ABSProfile extends AbstractProfile {

    private final static StrategyFactory DEFAULT =
            new ABSDLStrategy.Factory();
    public static final UIConfiguration UNPARSER = new ABSUIConfiguration();

    public ABSProfile() {
        super("standardRulesABS.key", ABSProof.class,
                DefaultImmutableSet.<GoalChooserBuilder>nil().
                add(new DefaultGoalChooserBuilder()).
                add(new DepthFirstGoalChooserBuilder()));
    }

    @Override
    public AbstractInitConfig createInitConfig(IServices services,
            Profile profile) {
        return new ABSInitConfig((ABSServices) services, profile);
    }

    @Override
    public ABSServices createServices(KeYExceptionHandler handler) {
        return new ABSServices(handler);
    }

    @Override
    public StrategyFactory getDefaultStrategyFactory() {
        return DEFAULT;
    }

    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        ImmutableSet<StrategyFactory> set = super.getStrategyFactories();
        set = set.add(DEFAULT);
        return set;
    }

    @Override
    public UIConfiguration getUIConfiguration() {
        return UNPARSER;
    }

    @Override
    public String name() {
        return "ABS Profile";
    }
}
