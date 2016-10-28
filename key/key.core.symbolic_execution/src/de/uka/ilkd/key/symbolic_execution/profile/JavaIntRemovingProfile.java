package de.uka.ilkd.key.symbolic_execution.profile;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.symbolic_execution.strategy.JavaIntRemovingStrategy;

public class JavaIntRemovingProfile extends JavaProfile {

    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        ImmutableSet<StrategyFactory> set = DefaultImmutableSet.<StrategyFactory>nil();
        set = set.add(DEFAULT);
        return set;
    }

   
   /**
     * returns the strategy factory for the default strategy of this profile
     */
    public StrategyFactory getDefaultStrategyFactory() {
    	return new JavaIntRemovingStrategy.JavaIntRemovingStrategyFactory();
    }

    /**
     * returns true if strategy <code>strategyName</code> may be
     * used with this profile.
     * @return supportedStrategies()->exists(s | s.name.equals(strategyName))
     */
    public boolean supportsStrategyFactory(Name strategyName) {
    	return strategyName.equals(JavaIntRemovingStrategy.NAME);
    }

    /**
     * returns the StrategyFactory for strategy <code>strategyName</code>
     * @param strategyName the Name of the strategy
     * @return the StrategyFactory to build the demanded strategy
     */
    public StrategyFactory getStrategyFactory(Name strategyName) {
    	if (supportsStrategyFactory(strategyName)) {
    		return getDefaultStrategyFactory(); 
    	}
    	throw new IllegalArgumentException("Not supported factory for strategy " + strategyName);
    }

}
