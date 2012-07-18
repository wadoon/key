package de.uka.ilkd.keyabs.init;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.proof.DefaultGoalChooserBuilder;
import de.uka.ilkd.key.proof.DepthFirstGoalChooserBuilder;
import de.uka.ilkd.key.proof.GoalChooserBuilder;
import de.uka.ilkd.key.proof.init.AbstractInitConfig;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.proof.ABSProof;

public class ABSProfile extends AbstractProfile {

    private final static StrategyFactory DEFAULT =
            new JavaCardDLStrategy.Factory();

    public ABSProfile() {
            super("standardRulesABS.key", ABSProof.class,
                    DefaultImmutableSet.<GoalChooserBuilder>nil().
                    add(new DefaultGoalChooserBuilder()).
                    add(new DepthFirstGoalChooserBuilder()));
    }

    @Override
    public String name() {
        return "ABS Profile";
    }

    @Override
    public StrategyFactory getDefaultStrategyFactory() {
        return DEFAULT;
    }

    @Override
    public ABSServices createServices(KeYExceptionHandler handler) {
        return new ABSServices(handler);
    }

    @Override
    public AbstractInitConfig createInitConfig(IServices services,
            Profile profile) {
        return new ABSInitConfig((ABSServices) services, profile);
    }
}
