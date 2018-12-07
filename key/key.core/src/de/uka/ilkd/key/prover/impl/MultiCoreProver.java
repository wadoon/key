package de.uka.ilkd.key.prover.impl;

import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.StopCondition;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.strategy.StrategyProperties;

public class MultiCoreProver extends AbstractProverCore {

    private Proof proof;
    private SchedulingGoalChooser goalChooser;
    private StopCondition stopCondition;

    /** number of closed goals */
    private final AtomicInteger closedGoals = new AtomicInteger(0);

    /** number of rules automatically applied */
    protected final AtomicInteger countApplied = new AtomicInteger(0);

    /** number of currently running tasks */
    protected final AtomicInteger numberOfTasks = new AtomicInteger(0);

    private int maxApplications;
    private long startTime = 0;
    private long timeout = -1;

    private final ExecutorService threadpool = new ThreadPoolExecutor(6, 8, 0, TimeUnit.SECONDS, new LinkedBlockingQueue<Runnable>());
    private final ExecutorCompletionService<SingleRuleApplicationInfo> completionService = new ExecutorCompletionService<>(threadpool);
    private boolean hasBeenInterrupted;

    class ProverTask implements Callable<SingleRuleApplicationInfo> {

        private final Goal goal;

        public ProverTask(Goal goal) {
            this.goal = goal;
        }

        @Override
        public SingleRuleApplicationInfo call() throws Exception {
            try {
                synchronized(goal) {
                    return proveGoal();
                }
            } catch (final Throwable t) {
                t.printStackTrace();
                throw t;
            }
        }

        /**
         * tries to prove the goal of this task as long as rules are applicable, the stopcondition
         * does not hold and it is not interrupted by the user
         * @return the result of the run
         */
        private SingleRuleApplicationInfo proveGoal() {
            RuleApp               app = null;
            SingleRuleApplicationInfo result = null;
            do {
                // check if goal is to be continued
                if (!stopCondition.isGoalAllowed(maxApplications,
                        timeout, proof, startTime, countApplied.get(), goal)) {
                    result = new SingleRuleApplicationInfo(
                            stopCondition.getGoalNotAllowedMessage(maxApplications, timeout, proof,
                                    startTime, countApplied.get(), goal),
                            goal, null);
                } else {

                    app = goal.getRuleAppManager().next();

                    //Hack: built in rules may become applicable without BuiltInRuleAppIndex noticing---->
                    if(app == null) {
                        goal.ruleAppIndex().scanBuiltInRules(goal);
                        app = goal.getRuleAppManager().next();
                    }
                    //<-------

                    if (app == null) {
                        result = new SingleRuleApplicationInfo("No more rules "
                                + "automatically applicable to this goal.", goal, app);
                    } else {
                        assert goal != null;

                        goal.apply(app);

                        final int nrAppliedRules = countApplied.incrementAndGet();
                        fireTaskProgress (nrAppliedRules);

                        if (goal.node().isClosed()) {
                            closedGoals.incrementAndGet();
                            result = new SingleRuleApplicationInfo(goal, app);
                        } else {
                            if (stopCondition.shouldStop(maxApplications, timeout, proof,
                                    startTime, nrAppliedRules, goal)) {
                                result = new SingleRuleApplicationInfo(stopCondition.
                                        getStopMessage(maxApplications, timeout, proof, startTime,
                                                countApplied.get(), goal), goal, app);
                            }
                        }
                    }
                }
            } while (!Thread.interrupted() && result == null);
            if (result == null) {
                result = new SingleRuleApplicationInfo("Prover task has been interrupted", goal, app);
            }
            return result;
        }
    }


    public MultiCoreProver() {}

    @Override
    public ApplyStrategyInfo start(Proof proof, Goal goal) {
        return start(proof, ImmutableSLList.<Goal>nil());
    }

    @Override
    public ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals) {
        return start(proof, goals, proof.getSettings().getStrategySettings());
    }

    @Override
    public ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals,
            StrategySettings settings) {
        final boolean stopAtFirstNonCloseableGoal =
                proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties().getProperty(
                        StrategyProperties.STOPMODE_OPTIONS_KEY)
                .equals(StrategyProperties.STOPMODE_NONCLOSE);
        return start(proof, goals, settings.getMaxSteps(), settings.getTimeout(), stopAtFirstNonCloseableGoal);
    }

    @Override
    public synchronized ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals,
            int maxSteps, long timeout, boolean stopAtFirstNonCloseableGoal) {
        this.proof = proof;
        this.stopCondition = proof.getSettings().getStrategySettings().getApplyStrategyStopCondition();
        this.maxApplications = stopCondition.getMaximalWork(maxSteps, timeout, proof);
        this.timeout = proof.getSettings().getStrategySettings().getTimeout();
        initGoalChooser(goals);


        final ApplyStrategyInfo result = run(proof, stopAtFirstNonCloseableGoal);

        proof.addAutoModeTime(result.getTime());
        fireTaskFinished (new DefaultTaskFinishedInfo(this, result, proof, result.getTime(),
                result.getAppliedRuleApps(),
                result.getClosedGoals()));
        return result;
    }

    private ApplyStrategyInfo run(Proof proof, boolean stopAtFirstNonCloseableGoal) {
        long time;
        SingleRuleApplicationInfo info = null;
        fireTaskStarted(maxApplications);

        startTime = System.currentTimeMillis();

        goalChooser.schedule();

        Goal exitGoal = null;
        try {
            boolean shouldStop = proof.closed();
            while (!shouldStop && numberOfTasks.get() != 0) {
                final Future<SingleRuleApplicationInfo> result = completionService.take();
                numberOfTasks.decrementAndGet();
                info = result.get();
                goalChooser.removeGoal(info.getGoal());
                if (!info.isSuccess()) {
                    if (stopAtFirstNonCloseableGoal) {
                        shouldStop  = true;
                    }
                    exitGoal = info.getGoal();
                }
                shouldStop |= (hasBeenInterrupted || Thread.interrupted());
            }
        } catch (InterruptedException | ExecutionException e) {
            e.printStackTrace();
            hasBeenInterrupted = true;
            return new ApplyStrategyInfo((e.getCause() != null ? e.getCause().getMessage(): "Proof Search Cancelled"), proof, e,
                    null, System.currentTimeMillis() - startTime, countApplied.get(), closedGoals.get());
        } catch (final Throwable t) {
            t.printStackTrace();
        } finally {
            time = System.currentTimeMillis() - startTime;
            shutdown();
            try {
                threadpool.awaitTermination(2, TimeUnit.SECONDS);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        return new ApplyStrategyInfo(info == null ? "" : info.message(), proof, null, exitGoal,
                time, countApplied.get(), closedGoals.get());
    }

    private void shutdown() {
        if (!threadpool.isTerminated()) {
            threadpool.shutdown();
            try {
                if (!threadpool.awaitTermination(600, TimeUnit.MILLISECONDS)) {
                    threadpool.shutdownNow();
                }
            } catch (final InterruptedException e) {
                threadpool.shutdownNow();
            }
        }
    }

    private void initGoalChooser(ImmutableList<Goal> goals) {
        goalChooser = new MultiCoreChooser(this);
        goalChooser.init(proof, goals);
    }

    @Override
    public void clear() {
        super.clear();
        shutdown();
        goalChooser.dispose();
        goalChooser = null;
        proof = null;
    }

    @Override
    public boolean hasBeenInterrupted() {
        return hasBeenInterrupted;
    }

    public void submit(Goal nextGoal) {
        if (!threadpool.isShutdown()) {
            numberOfTasks.incrementAndGet();
            completionService.submit(new ProverTask(nextGoal));
        }
    }
}
