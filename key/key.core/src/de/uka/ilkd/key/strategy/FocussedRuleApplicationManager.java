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

import org.key_project.common.core.logic.calculus.PIOPathIterator;
import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.FormulaTag;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.BinaryFeature;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppModPositionFeature;


/**
 * A rule app manager that ensures that rules are only applied to a certain
 * subterm within the proof (within a goal). The real work is delegated to a
 * second manager (delegate pattern), this class only filters rule applications
 */
public class FocussedRuleApplicationManager implements AutomatedRuleApplicationManager {

    private final AutomatedRuleApplicationManager delegate;
    public final QueueRuleApplicationManager rootManager;

    private final FormulaTag              focussedFormula;
    private final PosInOccurrence<Term>         focussedSubterm;

    private Goal                          goal;
    
    // Until <code>next</code> was called for the first time only rule
    // applications for the focussed formula are accepted, after that also
    // applications for other formulas. The idea is that then the rule index
    // caches are filled and further reported rules involve modified or new
    // formulas (this works at least for delegate
    // <code>QueueRuleApplicationManager</code>)
    private boolean                       onlyModifyFocussedFormula;
    
    private FocussedRuleApplicationManager (AutomatedRuleApplicationManager delegate,
                                    Goal goal,
                                    FormulaTag focussedFormula,
                                    PosInOccurrence<Term> focussedSubterm,
                                    boolean onlyModifyFocussedFormula) {
        this.delegate = delegate;
        this.rootManager = delegate instanceof QueueRuleApplicationManager
                ? (QueueRuleApplicationManager) delegate
                : ((FocussedRuleApplicationManager) delegate).rootManager;
        this.focussedFormula = focussedFormula;
        this.focussedSubterm = focussedSubterm;
        this.goal = goal;
        this.onlyModifyFocussedFormula = onlyModifyFocussedFormula;
    }
    
    public FocussedRuleApplicationManager (AutomatedRuleApplicationManager delegate,
                                   Goal goal,
                                   PosInOccurrence<Term> focussedSubterm) {
        this ( delegate,
               goal,
               goal.getFormulaTagManager ()
                   .getTagForPos ( focussedSubterm.topLevel () ),
               focussedSubterm,
               true );
        
        clearCache ();
    }

    @Override
    public void clearCache () {
        delegate.clearCache ();
    }

    @Override
    public AutomatedRuleApplicationManager copy () {
        return (AutomatedRuleApplicationManager)clone ();
    }

    @Override
    public Object clone () {
        return new FocussedRuleApplicationManager ( delegate.copy (),
                                            null,
                                            focussedFormula,
                                            focussedSubterm,
                                            onlyModifyFocussedFormula );
    }
    
    @Override
    public RuleApp<Term, Goal> peekNext () {
	return delegate.peekNext();
    } 

    @Override
    public RuleApp<Term, Goal> next () {
        final RuleApp<Term, Goal> app = delegate.next ();
        onlyModifyFocussedFormula = false;
        return app;
    }

    @Override
    public void setGoal (Goal p_goal) {
        goal = p_goal;
        delegate.setGoal ( p_goal );
    }

    @Override
    public void ruleAdded (RuleApp<Term, Goal> rule, PosInOccurrence<Term> pos) {
        if ( isRuleApplicationForFocussedFormula(rule, pos) ) {            
            delegate.ruleAdded ( rule, pos );
        }         
    }

    protected boolean isRuleApplicationForFocussedFormula(RuleApp<Term, Goal> rule,
            PosInOccurrence<Term> pos) {
        // filter the rule applications, only allow applications within the
        // focussed subterm or to other formulas that have been added after creation
        // of the manager (we rely on the fact that the caching rule indexes only
        // report rules for modified/added formulas anyway)
        
        final PosInOccurrence<Term> focFormula = getPIOForFocussedSubterm ();

        if ( focFormula != null && pos != null ) {
            if ( isSameFormula ( pos, focFormula ) ) {
                if ( !isBelow ( focFormula, pos ) || 
                		NonDuplicateAppModPositionFeature.INSTANCE.computeCost(rule, pos, goal).equals(BinaryFeature.TOP_COST))
                    // rule app within the focussed formula, but not within the
                    // focussed subterm
                    return false;
            } else {
                if ( onlyModifyFocussedFormula ) return false;
            }
        } else if ( onlyModifyFocussedFormula ) {
            return false;
        }
        return true;
    }

    
    @Override
    public void rulesAdded (ImmutableList<? extends RuleApp<Term, Goal>> rules, PosInOccurrence<Term> pos) {
        ImmutableList<RuleApp<Term, Goal>> applicableRules = ImmutableSLList.<RuleApp<Term, Goal>>nil();
        for (RuleApp<Term, Goal> r : rules) {
            if (isRuleApplicationForFocussedFormula(r, pos)) {
                applicableRules = applicableRules.prepend(r);
            }
        }
        
        delegate.rulesAdded ( applicableRules, pos );
    }

    
    private boolean isSameFormula (PosInOccurrence<Term> pio1,
                                   PosInOccurrence<Term> pio2) {
        return pio2.isInAntec () == pio1.isInAntec ()
               && pio2.sequentFormula ().equals ( pio1.sequentFormula () );
    }

    private PosInOccurrence<Term> getPIOForFocussedSubterm () {
        final PosInOccurrence<Term> formula =
            goal.getFormulaTagManager ().getPosForTag ( focussedFormula );

        if ( formula == null ) return null;

        return
            focussedSubterm
            .replaceConstrainedFormula ( formula.sequentFormula () );
    }
    
    private boolean isBelow (PosInOccurrence<Term> over, PosInOccurrence<Term> under) {
        final PIOPathIterator<Term> overIt = over.iterator ();
        final PIOPathIterator<Term> underIt = under.iterator ();

        while ( true ) {
            final int overChild = overIt.next ();
            final int underChild = underIt.next ();
            if ( overChild == -1 ) return true;
            if ( overChild != underChild ) return false;
        }
    }

    public AutomatedRuleApplicationManager getDelegate () {
        return delegate;
    }
}