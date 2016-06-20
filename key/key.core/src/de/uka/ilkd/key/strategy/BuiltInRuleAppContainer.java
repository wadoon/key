// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy;

import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.FormulaTag;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;


/**
 * Instances of this class are immutable
 */
public class BuiltInRuleAppContainer extends RuleAppContainer {

    /**
     * The position of the rule app in two different representations:
     * <code>positionTag</code> denotes the concerned formula and survives
     * modifications of the sequent and of parts of the formula, and
     * <code>applicationPosition</code> is the original position for which the
     * rule app was created
     */
    private final FormulaTag      positionTag;
    private final PosInOccurrence<Term, SequentFormula<Term>> applicationPosition;
    
    private final IBuiltInRuleApp bir;
    
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
        
    private BuiltInRuleAppContainer(IBuiltInRuleApp bir,
			     	    PosInOccurrence<Term, SequentFormula<Term>> pio,
			     	    RuleAppCost     cost,
			     	    Goal            goal) {
        super(bir, cost);
    	applicationPosition = pio;
    	positionTag 
    		= pio == null 
    	          ? null 
    	          : goal.getFormulaTagManager().getTagForPos(pio.topLevel());
        this.bir = bir;
    	assert !(pio != null && positionTag == null) 
    	       : "Formula " + pio + " does not exist";
    }
    
    
    

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * @return true iff the stored rule app is applicable for the given sequent,
     * i.e. if the bound position does still exist (if-formulas are not
     * considered)
     */
    private boolean isStillApplicable(Goal goal) {
	if(applicationPosition == null) {
	    return bir.rule().isApplicable(goal,  null);	    
	} else {
            final PosInOccurrence<Term, SequentFormula<Term>> topPos 
    		= goal.getFormulaTagManager().getPosForTag(positionTag);
            if(topPos == null) {
        	//the formula does not exist anymore, bail out
        	return false;
            } else {
                return topPos.sequentFormula()
                    .equals(applicationPosition.sequentFormula());
            }
	}
    }
    
    
    /**
     * Copied from FindTaclet.
     */
    private PosInOccurrence<Term, SequentFormula<Term>> getPosInOccurrence(Goal p_goal) {
    	final PosInOccurrence<Term, SequentFormula<Term>> topPos =
    	    p_goal.getFormulaTagManager().getPosForTag(positionTag);

	assert topPos != null;
	
	return applicationPosition.replaceConstrainedFormula
	    ( topPos.sequentFormula () );
    }    
    
    

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Create container for RuleApp.
     * @return container for the currently applicable BuiltInRuleApp,
     * the cost may be an instance of <code>TopRuleAppCost</code>.
     */
    static RuleAppContainer createAppContainer( 
	    					IBuiltInRuleApp bir,
	    					PosInOccurrence<Term, SequentFormula<Term>> pio,
	    					Goal goal,
	    					Strategy strategy ) {
        final RuleAppCost cost = strategy.computeCost(bir, pio, goal);

        final BuiltInRuleAppContainer container 
        	= new BuiltInRuleAppContainer(bir, pio, cost, goal);

        return container;
    }    
    
    /**
     * Create container for RuleApp.
     * @return container for the currently applicable BuiltInRuleApp,
     * the cost may be an instance of <code>TopRuleAppCost</code>.
     */
    static ImmutableList<RuleAppContainer> createInitialAppContainers( 
                            ImmutableList<IBuiltInRuleApp> birs,
                            PosInOccurrence<Term, SequentFormula<Term>> pio,
                            Goal goal,
                            Strategy strategy ) {
        ImmutableList<RuleAppContainer> result = ImmutableSLList.<RuleAppContainer>nil();
        
        for (IBuiltInRuleApp bir : birs) {
            result = result.prepend(createAppContainer(bir, pio, goal, strategy));
        }
        
        return result;
    }    
    
    

    @Override
    public ImmutableList<RuleAppContainer> createFurtherApps(
	    					Goal goal,
	    					Strategy strategy) {
        if(!isStillApplicable(goal)) {
            return ImmutableSLList.<RuleAppContainer>nil();
        }
        
        final PosInOccurrence<Term, SequentFormula<Term>> pio = getPosInOccurrence(goal);
        
        RuleAppContainer container = createAppContainer(bir, pio, goal, strategy);
        if(container.getCost() instanceof TopRuleAppCost) {
            return ImmutableSLList.<RuleAppContainer>nil();
        }
        return ImmutableSLList.<RuleAppContainer>nil().prepend(container);
    }
    

    @Override
    public RuleApp completeRuleApp(Goal goal, Strategy strategy) {
        if(!isStillApplicable(goal)) {
            return null;
        }
        
        final PosInOccurrence<Term, SequentFormula<Term>> pio = getPosInOccurrence (goal);
        if(!strategy.isApprovedApp(bir, pio, goal)) {
            return null;
        }                
        
        final BuiltInRule rule = bir.rule();
        IBuiltInRuleApp app = rule.createApp(pio, goal.proof().getServices());
	        
		if (!app.complete()) {
		    app = app.setIfInsts(bir.ifInsts());
		    // TODO: check for force ?
		    final boolean force = true;
			app = force? app.forceInstantiate(goal): app.tryToInstantiate(goal);
		}

		return app.complete() ? app : null;
    }
}