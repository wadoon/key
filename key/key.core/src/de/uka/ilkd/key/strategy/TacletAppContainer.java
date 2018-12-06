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

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.NoFindTaclet;
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

    protected static TacletAppContainer createContainer(NoPosTacletApp p_app,
            PosInOccurrence p_pio,
            Goal p_goal,
            boolean p_initial) {
        return createContainer ( p_app, p_pio, p_goal,
                p_goal.getGoalStrategy().computeCost ( p_app, p_pio, p_goal ),
                p_initial );
    }

    private static TacletAppContainer createContainer(NoPosTacletApp p_app,
            PosInOccurrence p_pio,
            Goal p_goal,
            RuleAppCost p_cost,
            boolean p_initial) {
        // This relies on the fact that the method <code>Goal.getTime()</code>
        // never returns a value less than zero
        final long        localage  = p_initial ? -1 : p_goal.getTime();
        if ( p_pio == null )
            return new NoFindTacletAppContainer ( p_app, p_cost, localage );
        else
            return new FindTacletAppContainer ( p_app, p_pio, p_cost, p_goal, localage );
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

    private static ExecutorService exServiceInit = Executors.newFixedThreadPool(4, new MyThreadFactory(Executors.defaultThreadFactory(), "init"));

    class InitComputationTask implements Runnable {

        private Goal p_goal;
        private NoPosTacletApp app;
        private RuleAppCostCollector collector;
        public InitComputationTask(Goal p_goal, NoPosTacletApp app, RuleAppCostCollector collector) {
            this.p_goal = p_goal;
            this.app = app;
            this.collector = collector;
        }
        @Override
        public void run() {
            p_goal.getGoalStrategy().instantiateApp ( app,
                    getPosInOccurrence ( p_goal ),
                    p_goal,
                    collector );
        }

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
        //        final ImmutableList<RuleAppContainer>[] resA =  new ImmutableList[] { targetList };
        final ArrayBlockingQueue<RuleAppContainer> resArrayQueue = new ArrayBlockingQueue<>(10000);
        final RuleAppCostCollector collector =
                new RuleAppCostCollector () {
            @Override
            public void collect(RuleApp newApp, RuleAppCost cost) {
                if (cost instanceof TopRuleAppCost) return;
                addContainer ( (NoPosTacletApp)newApp,
                        p_goal,
                        cost, resArrayQueue );
            }
        };
        Future<?> future = exServiceInit.submit(new InitComputationTask(p_goal, app, collector));
        try {
            future.get();
        }
        catch (InterruptedException | ExecutionException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        //        p_goal.getGoalStrategy().instantiateApp ( app,
        //                getPosInOccurrence ( p_goal ),
        //                p_goal,
        //                collector );
        for (RuleAppContainer container : resArrayQueue) {
            targetList = targetList.prepend(container);
        }
        return targetList;
    }

    /**
     * Create a container object for the given taclet app, provided that the app
     * is <code>sufficientlyComplete</code>, and add the container to
     * <code>targetList</code>
     */
    private ImmutableList<RuleAppContainer> addContainer(NoPosTacletApp app,
            ImmutableList<RuleAppContainer> targetList,
            Goal p_goal) {
        return targetList.prepend ( TacletAppContainer
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
    private void addContainer(NoPosTacletApp app,
            Goal p_goal,
            RuleAppCost cost, Collection<RuleAppContainer> newApps) {
        if ( !sufficientlyCompleteApp ( app ) ) return;
        newApps.add ( TacletAppContainer
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
        return createContainer ( getTacletApp (),
                getPosInOccurrence ( p_goal ),
                p_goal,
                false );
    }

    /**
     * Create containers for NoFindTaclets.
     */
    static RuleAppContainer createAppContainers( NoPosTacletApp p_app, Goal p_goal ) {
        return createAppContainers ( p_app, null, p_goal );
    }
    private static ExecutorService exService = Executors.newFixedThreadPool(4, new MyThreadFactory(Executors.defaultThreadFactory(), "cost"));
    static class CostComputationTask implements Callable<TacletAppContainer> {

        private Goal p_goal;
        private NoPosTacletApp p_app;
        private PosInOccurrence p_pio;
        public CostComputationTask(Goal p_goal, NoPosTacletApp p_app, PosInOccurrence p_pio) {
            this.p_goal = p_goal;
            this.p_app = p_app;
            this.p_pio = p_pio;
        }
        @Override
        public TacletAppContainer call() throws Exception {
            final RuleAppCost cost = p_goal.getGoalStrategy().computeCost ( p_app, p_pio, p_goal );
            final TacletAppContainer container = createContainer ( p_app, p_pio, p_goal, cost, true );

            return container;
        }

    }
    protected static ImmutableList<RuleAppContainer> createInitialAppContainers(ImmutableList<NoPosTacletApp> p_app,
            PosInOccurrence p_pio, Goal p_goal) {

        ImmutableList<RuleAppContainer> result = ImmutableSLList.<RuleAppContainer>nil();
        List<CostComputationTask> list = new LinkedList<>();
        while (!p_app.isEmpty()) {
            CostComputationTask task = new CostComputationTask(p_goal, p_app.head(), p_pio);
            list.add(task);
            p_app = p_app.tail();
        }
        try {
            List<Future<TacletAppContainer>> futures = exService.invokeAll(list);

            for (Future<TacletAppContainer> future : futures) {
                TacletAppContainer container = future.get();
                if (container != null) {
                    result = result.prepend(container);
                }
            }
        }
        catch (InterruptedException | ExecutionException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        //            final RuleAppCost cost = p_goal.getGoalStrategy().computeCost ( p_app.head(), p_pio, p_goal );
        //            final TacletAppContainer container = createContainer ( p_app.head(), p_pio, p_goal, cost, true );
        //            if (container != null) { result = result.prepend(container); }
        //            p_app = p_app.tail();
        return result;
    }

    /**
     * Create containers for FindTaclets or NoFindTaclets.
     * @param p_app if <code>p_pio</code> is null, <code>p_app</code> has to be
     * a <code>TacletApp</code> for a <code>NoFindTaclet</code>,
     * otherwise for a <code>FindTaclet</code>.
     * @return list of containers for currently applicable TacletApps, the cost
     * may be an instance of <code>TopRuleAppCost</code>.
     */
    static RuleAppContainer createAppContainers
    ( NoPosTacletApp  p_app,
            PosInOccurrence p_pio,
            Goal            p_goal ) {
        if ( !( p_pio == null
                ? p_app.taclet () instanceof NoFindTaclet
                        : p_app.taclet () instanceof FindTaclet ) )
            // faster than <code>assertTrue</code>
            Debug.fail ( "Wrong type of taclet " + p_app.taclet () );

        // Create an initial container for the given taclet; the if-formulas of
        // the taclet are only matched lazy (by <code>createFurtherApps()</code>
        return createContainer ( p_app, p_pio, p_goal, true );
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

        final TacletApp app2 = getTacletApp();
        PosInOccurrence pio = getPosInOccurrence(p_goal);

        Future<Boolean> future = exService.submit(new Callable<Boolean>() {

            @Override
            public Boolean call() throws Exception {
                // TODO Auto-generated method stub
                return !p_goal.getGoalStrategy().isApprovedApp(app2, pio, p_goal);
            }

        });
        try {
            if (future.get()) {
                return null;
            }
        }
        catch (InterruptedException | ExecutionException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        TacletApp app = app2;
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