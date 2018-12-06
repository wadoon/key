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

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;

/**
 * Instances of this class are immutable
 */
public abstract class TacletAppContainer extends RuleAppContainer {

    // Implementation note (DB 21/02/2014):
    // It is unlikely that we ever reach 2^31 proof nodes,
    // so age could be changed from long to int.
    // My benchmark tests however suggest that this would not
    // save any memory (at the moment).
    // This is because Java's memory alingment.

    private final long age;

    protected TacletAppContainer ( RuleApp     p_app,
            RuleAppCost p_cost,
            long        p_age ) {
        super ( p_app, p_cost );
        age = p_age;
    }

    protected NoPosTacletApp getTacletApp () {
        return (NoPosTacletApp)getRuleApp();
    }

    public long getAge () {
        return age;
    }

    private ImmutableList<NoPosTacletApp> incMatchIfFormulas (Goal p_goal) {
        final IfInstantiator instantiator = new IfInstantiator (this, p_goal );
        instantiator.findIfFormulaInstantiations ();
        return instantiator.getResults ();
    }

    /**
     * Create a list of new RuleAppContainers that are to be
     * considered for application.
     */
    @Override
    public final ImmutableList<RuleAppContainer> createFurtherApps(Goal p_goal) {
        if (!isStillApplicable(p_goal)
                || (getTacletApp().ifInstsComplete() && !ifFormulasStillValid(p_goal))) {
            return ImmutableSLList.nil();
        }

        final TacletAppContainer newCont = createContainer(p_goal);
        if (newCont.getCost() instanceof TopRuleAppCost) {
            return ImmutableSLList.nil();
        }

        ImmutableList<RuleAppContainer> res = ImmutableSLList.<RuleAppContainer>nil().prepend(newCont);

        if (getTacletApp().ifInstsComplete()) {
            res = addInstances(getTacletApp(), res, p_goal);
        } else {
            for (NoPosTacletApp tacletApp : incMatchIfFormulas(p_goal)) {
                final NoPosTacletApp app = tacletApp;
                res = addContainer(app, res, p_goal);
                res = addInstances(app, res, p_goal);
            }
        }

        return res;
    }

    /**
     * Add all instances of the given taclet app (that are possibly produced
     * using method <code>instantiateApp</code> of the strategy) to
     * <code>targetList</code>
     */
    private ImmutableList<RuleAppContainer> addInstances( NoPosTacletApp app,
            ImmutableList<RuleAppContainer> targetList,
            Goal p_goal) {
        if ( app.uninstantiatedVars ().size () == 0 ) return targetList;
        return instantiateApp ( app, targetList, p_goal );
    }

    /**
     * Use the method <code>instantiateApp</code> of the strategy for choosing
     * the values of schema variables that have not been instantiated so far
     */
    private ImmutableList<RuleAppContainer> instantiateApp(NoPosTacletApp app,
            ImmutableList<RuleAppContainer> targetList,
            final Goal p_goal) {
        // just for being able to modify the result-list in an
        // anonymous class
        @SuppressWarnings("unchecked")
        final ImmutableList<RuleAppContainer>[] resA =  new ImmutableList[] { targetList };

        final RuleAppCostCollector collector =
                new RuleAppCostCollector () {
            @Override
            public void collect(RuleApp newApp, RuleAppCost cost) {
                if (cost instanceof TopRuleAppCost) return;
                resA[0] = addContainer ( (NoPosTacletApp)newApp,
                        resA[0],
                        p_goal,
                        cost );
            }
        };
        p_goal.getGoalStrategy().instantiateApp ( app,
                getPosInOccurrence ( p_goal ),
                p_goal,
                collector );

        return resA[0];
    }

    /**
     * Create a container object for the given taclet app, provided that the app
     * is <code>sufficientlyComplete</code>, and add the container to
     * <code>targetList</code>
     */
    private ImmutableList<RuleAppContainer> addContainer(NoPosTacletApp app,
            ImmutableList<RuleAppContainer> targetList,
            Goal p_goal) {
        return targetList.prepend ( TacletAppContainerBuilder
                .createContainer ( app,
                        getPosInOccurrence ( p_goal ),
                        p_goal,
                        false ) );
    }

    /**
     * Create a container object for the given taclet app, provided that the app
     * is <code>sufficientlyComplete</code>, and add the container to
     * <code>targetList</code>
     */
    private ImmutableList<RuleAppContainer> addContainer(NoPosTacletApp app,
            ImmutableList<RuleAppContainer> targetList,
            Goal p_goal,
            RuleAppCost cost) {
        if ( !sufficientlyCompleteApp ( app ) ) return targetList;
        return targetList.prepend ( TacletAppContainerBuilder
                .createContainer ( app,
                        getPosInOccurrence ( p_goal ),
                        p_goal,
                        cost,
                        false ) );
    }

    private static boolean sufficientlyCompleteApp(NoPosTacletApp app) {
        final ImmutableSet<SchemaVariable> needed = app.uninstantiatedVars ();
        if ( needed.size () == 0 ) return true;
        for (SchemaVariable aNeeded : needed) {
            if ( app.isInstantiationRequired(aNeeded) ) {
                return false;
            }
        }
        return true;
    }

    private TacletAppContainer createContainer (Goal p_goal) {
        return TacletAppContainerBuilder.createContainer ( getTacletApp (),
                getPosInOccurrence ( p_goal ),
                p_goal,
                false );
    }

    /**
     * @return true iff instantiation of the if-formulas of the stored taclet
     * app exist and are valid are still valid, i.e. the referenced formulas
     * still exist
     */
    protected boolean ifFormulasStillValid ( Goal p_goal ) {
        if ( getTacletApp().taclet().ifSequent().isEmpty() )
            return true;
        if ( !getTacletApp().ifInstsComplete() )
            return false;

        final Iterator<IfFormulaInstantiation> it =
                getTacletApp().ifFormulaInstantiations().iterator();
        final Sequent seq = p_goal.sequent();

        while ( it.hasNext () ) {
            final IfFormulaInstantiation ifInst2 = it.next ();
            if ( !( ifInst2 instanceof IfFormulaInstSeq ) )
                // faster than assertTrue
                Debug.fail ( "Don't know what to do with the " +
                        "if-instantiation " + ifInst2 );
            final IfFormulaInstSeq ifInst = (IfFormulaInstSeq)ifInst2;
            if ( !( ifInst.inAntec() ? seq.antecedent() : seq.succedent() )
                    .contains ( ifInst.getConstrainedFormula() ) )
                return false;
        }

        return true;
    }

    /**
     * @return true iff the stored rule app is applicable for the given sequent,
     * i.e. if the find-position does still exist (if-formulas are not
     * considered)
     */
    protected abstract boolean isStillApplicable ( Goal p_goal );

    protected PosInOccurrence getPosInOccurrence ( Goal p_goal ) {
        return null;
    }

    /**
     * Create a <code>RuleApp</code> that is suitable to be applied
     * or <code>null</code>.
     */
    @Override
    public TacletApp completeRuleApp(Goal p_goal) {
        if (!(isStillApplicable(p_goal) && ifFormulasStillValid(p_goal))) {
            return null;
        }

        TacletApp app = getTacletApp();
        PosInOccurrence pio = getPosInOccurrence(p_goal);
        if (!p_goal.getGoalStrategy().isApprovedApp(app, pio, p_goal)) {
            return null;
        }

        Services services = p_goal.proof().getServices();
        if (pio != null) {
            app = app.setPosInOccurrence(pio, services);
            if (app == null) {
                return null;
            }
        }

        if (!app.complete()) {
            return app.tryToInstantiate(services.getOverlay(p_goal.getLocalNamespaces()));
        } else if (!app.isExecutable(services)) {
            return null;
        } else {
            return app;
        }
    }
}