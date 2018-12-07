package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.Pair;

public class TacletAppContainerBuilder {
    private static ExecutorService exService = Executors.newFixedThreadPool(4);// ,
    // new
    // MyThreadFactory(Executors.defaultThreadFactory(),
    // "cost"));

    private static RuleAppContainer calculateCost(Goal p_goal, NoPosTacletApp app, PosInOccurrence p_pio) {
        final RuleAppCost cost = p_goal.getGoalStrategy().computeCost(app, p_pio, p_goal);
        return createContainer(app, p_pio, p_goal, cost, true);
    }

    protected static Iterable<RuleAppContainer> createInitialAppContainers(
            ImmutableList<NoPosTacletApp> p_app, PosInOccurrence p_pio,
            Goal p_goal) {

        ArrayList<RuleAppContainer> result = new ArrayList<>();
        for (NoPosTacletApp app : p_app) {
            // sequential
            result.add(calculateCost(p_goal, app, p_pio));
        }
        return result;
    }

    protected static Iterable<Future<RuleAppContainer>> createInitialAppContainers(
            ImmutableList<Pair<PosInOccurrence, ImmutableList<NoPosTacletApp>>> rules,
            final Goal p_goal) {

        List<Future<RuleAppContainer>> futures = new ArrayList<>();
        for (Pair<PosInOccurrence, ImmutableList<NoPosTacletApp>> pair : rules) {
            ImmutableList<NoPosTacletApp> apps = pair.second;
            final PosInOccurrence pio = pair.first;
            for (final NoPosTacletApp app : apps) {
                futures.add(exService.submit(() -> { return calculateCost(p_goal, app, pio); }));
            }
        }

        return futures;
    }

    protected static TacletAppContainer createContainer(NoPosTacletApp p_app,
            PosInOccurrence p_pio, Goal p_goal, boolean p_initial) {
        return TacletAppContainerBuilder.createContainer(p_app, p_pio, p_goal,
                p_goal.getGoalStrategy().computeCost(p_app, p_pio, p_goal),
                p_initial);
    }

    static TacletAppContainer createContainer(NoPosTacletApp p_app,
            PosInOccurrence p_pio, Goal p_goal, RuleAppCost p_cost,
            boolean p_initial) {
        // This relies on the fact that the method <code>Goal.getTime()</code>
        // never returns a value less than zero
        final long localage = p_initial ? -1 : p_goal.getTime();
        if (p_pio == null) {
            return new NoFindTacletAppContainer(p_app, p_cost, localage);
        }
        else {
            return new FindTacletAppContainer(p_app, p_pio, p_cost, p_goal,
                    localage);
        }
    }

    /**
     * Create containers for NoFindTaclets.
     */
    static RuleAppContainer createAppContainers(NoPosTacletApp p_app,
            Goal p_goal) {
        return TacletAppContainerBuilder.createAppContainers(p_app, null,
                p_goal);
    }

    /**
     * Create containers for FindTaclets or NoFindTaclets.
     *
     * @param p_app
     *            if <code>p_pio</code> is null, <code>p_app</code> has to be a
     *            <code>TacletApp</code> for a <code>NoFindTaclet</code>,
     *            otherwise for a <code>FindTaclet</code>.
     * @return list of containers for currently applicable TacletApps, the cost
     *         may be an instance of <code>TopRuleAppCost</code>.
     */
    static RuleAppContainer createAppContainers(NoPosTacletApp p_app,
            PosInOccurrence p_pio, Goal p_goal) {
        if (!(p_pio == null ? p_app.taclet() instanceof NoFindTaclet
                : p_app.taclet() instanceof FindTaclet)) {
            // faster than <code>assertTrue</code>
            Debug.fail("Wrong type of taclet " + p_app.taclet());
        }

        // Create an initial container for the given taclet; the if-formulas of
        // the taclet are only matched lazy (by <code>createFurtherApps()</code>
        return createContainer(p_app, p_pio, p_goal, true);
    }

    // protected static ImmutableList<RuleAppContainer>
    // createInitialAppContainers(ImmutableList<NoPosTacletApp> p_app,
    // PosInOccurrence p_pio, Goal p_goal) {
    //
    // ImmutableList<RuleAppContainer> result =
    // ImmutableSLList.<RuleAppContainer>nil();
    // while (!p_app.isEmpty()) {
    // final RuleAppCost cost = p_goal.getGoalStrategy().computeCost (
    // p_app.head(), p_pio, p_goal );
    // final TacletAppContainer container = createContainer ( p_app.head(),
    // p_pio, p_goal, cost, true );
    // if (container != null) { result = result.prepend(container); }
    // p_app = p_app.tail();
    // }
    // return result;
    // }
}
