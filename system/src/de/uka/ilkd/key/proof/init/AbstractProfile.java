// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// 

package de.uka.ilkd.key.proof.init;

import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.DefaultGoalChooserBuilder;
import de.uka.ilkd.key.proof.DepthFirstGoalChooserBuilder;
import de.uka.ilkd.key.proof.GoalChooserBuilder;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooserBuilder;

public abstract class AbstractProfile<S extends IServices, IC extends InitConfig<S, IC>> implements Profile<S, IC> {

    private final RuleCollection       standardRules;

    private final ImmutableSet<StrategyFactory> strategies;

    private final ImmutableSet<String> supportedGC;
    private final ImmutableSet<GoalChooserBuilder> supportedGCB;

    private GoalChooserBuilder prototype;

    protected AbstractProfile(String standardRuleFilename,
            Class<?> relativeRulesPath,
            ImmutableSet<GoalChooserBuilder> supportedGCB) {

        standardRules = new RuleCollection(RuleSource
                .initRuleFile(relativeRulesPath, standardRuleFilename),
                initBuiltInRules());
        strategies = getStrategyFactories();
        this.supportedGCB = supportedGCB;
        this.supportedGC = extractNames(supportedGCB);
        this.prototype = getDefaultGoalChooserBuilder();
        assert( this.prototype!=null );

    }

    
    private static
        ImmutableSet<String> extractNames(ImmutableSet<GoalChooserBuilder> supportedGCB) {

        ImmutableSet<String> result = DefaultImmutableSet.<String>nil();

        final Iterator<GoalChooserBuilder> it = supportedGCB.iterator();
        while (it.hasNext()) {
            result  = result.add(it.next().name());
        }

        return result;
    }

    protected AbstractProfile(String standardRuleFilename, Class<?> relativeRulesPath) {
        this(standardRuleFilename, relativeRulesPath,
                DefaultImmutableSet.<GoalChooserBuilder>nil().
                add(new DefaultGoalChooserBuilder()).
                add(new DepthFirstGoalChooserBuilder()).
                add(new SymbolicExecutionGoalChooserBuilder()));
    }

    @Override
    public RuleCollection getStandardRules() {
        return standardRules;
    }

    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        return DefaultImmutableSet.<StrategyFactory>nil();
    }

    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        ImmutableList<BuiltInRule> builtInRules = ImmutableSLList.<BuiltInRule>nil();

	
	//Collection<SMTRule> rules = SMTSettings.getInstance().getSMTRules();
        
	//for(SMTRule rule : rules){
	  //  builtInRules = builtInRules.prepend(rule);  
	//}     
        
     
        
        
        
        return builtInRules;
    }


    @Override
    public ImmutableSet<StrategyFactory> supportedStrategies() {
        return strategies;
    }

    @Override
    public boolean supportsStrategyFactory(Name strategy) {
        return getStrategyFactory(strategy) != null;
    }

    @Override
    public StrategyFactory getStrategyFactory(Name n) {
        Iterator<StrategyFactory> it = getStrategyFactories().iterator();
        while (it.hasNext()) {
            final StrategyFactory sf = it.next();
            if (sf.name().equals(n)) {
                return sf;
            }
        }
        return null;
    }

    /**
     * returns the names of the supported goal chooser
     * builders
     */
    @Override
     public ImmutableSet<String> supportedGoalChoosers() {
         return supportedGC;
     }

     /**
      * returns the default builder for a goal chooser
      * @return this implementation returns a new instance of
      * {@link DefaultGoalChooserBuilder}
      */
    @Override
     public GoalChooserBuilder getDefaultGoalChooserBuilder() {
         return new DefaultGoalChooserBuilder();
     }

     /**
      * sets the user selected goal chooser builder to be used as prototype
      * @throws IllegalArgumentException if a goal chooser of the given name is not
      *  supported
      */
    @Override
     public void setSelectedGoalChooserBuilder(String name) {

         this.prototype = lookupGC(name);

         if (this.prototype == null) {
             throw new IllegalArgumentException("Goal chooser:" + name +
                     " is not supported by this profile.");
         }
     }

     /**
      * looks up the demanded goal chooser is supported and returns a
      * new instance if possible otherwise <code>null</code> is returned
      *
      * @param name the String with the goal choosers name
      * @return a new instance of the builder or <code>null</code> if the
      * demanded chooser is not supported
      */
     protected GoalChooserBuilder lookupGC(String name) {
        final Iterator<GoalChooserBuilder> it  = supportedGCB.iterator();
        while (it.hasNext()) {
            final GoalChooserBuilder supprotedGCB = it.next();
            if (supprotedGCB.name().equals(name)) {
                return supprotedGCB.copy();
            }
        }
        return null;
    }

    /**
      * returns a copy of the selected goal chooser builder
      */
     @Override
     public GoalChooserBuilder getSelectedGoalChooserBuilder(){
        return prototype.copy();
     }

     /**
      * any standard rule has is by default justified by an axiom rule
      * justification
      * @return the justification for the standard rules
      */
     @Override
     public RuleJustification getJustification(Rule r) {
         return AxiomJustification.INSTANCE;
     }

     /**
      * sets the given settings to some default depending on the profile
      */
     @Override
     public void updateSettings(ProofSettings settings) {
	 //settings.getSMTSettings().updateSMTRules(this);
     }
     
     
     @Override
     public String getInternalClassDirectory() {
 	return "";
     }     


     @Override
     public String getInternalClasslistFilename() {
	 return "JAVALANG.TXT";
     }
}
