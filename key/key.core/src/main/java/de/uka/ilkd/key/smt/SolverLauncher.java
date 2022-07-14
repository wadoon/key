package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;

/**
 * IN ORDER TO START THE SOLVERS USE THIS CLASS.<br>
 * There are two cases how the solvers can be started:<br>
 * <br>
 * 1. Case: Starting the solvers synchronously<br>
 * <br>
 * First Step: Create the SMT problem:<br>
 * <code>SMTProblem problem = new SMTProblem(g); // g can be either a goal or term</code>
 * <br>
 * <br>
 * Second Step: Create the launcher object:<br>
 * <code>SolverLauncher launcher = new SolverLauncher(new SMTSettings(){...});</code>
 * <br>
 * <br>
 * Third Step: Launch the solvers you want to execute<br>
 * <code>launcher.launch(problem, services,SolverType.Z3_SOLVER,SolverType.YICES_SOLVER);</code>
 * <br>
 * <br>
 * Forth Step: Get the final result<br>
 * <code>return problem.getFinalResult();</code><br>
 * <br>
 * In case that you want to access the result of each solver:<br>
 *
 * <pre>
 * for (SMTSolver solver : problem.getSolvers()) {
 *     solver.getFinalResult();
 * }
 * </pre>
 *
 * <br>
 * <p>
 * 2. Case: Starting the solvers asynchronously:<br>
 * <br>
 *
 * <pre>
 * Thread thread = new Thread(new Runnable() {
 * public void run() {
 *   SMTProblem final problem = new SMTProblem(...);
 *   SolverLauncher launcher = new SolverLauncher(new SMTSettings(...));
 *   launcher.addListener(new SolverLauncherListener(){
 *          public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> problemSolvers){
 *              // do something with the results here...
 *              problem.getFinalResult();
 *              // handling the problems that have occurred:
 *              for(SMTSolver solver : problemSolvers){
 *                  solver.getException();
 *                  ...
 *            }
 *          }
 *          public void launcherStarted(Collection<SMTProblem> problems,
 *                                      Collection<SolverType> solverTypes,
 *                                      SolverLauncher launcher);
 *             });
 *   launcher.launch(problem,services,SolverType.Z3_SOLVER,SolverType.YICES_SOLVER);
 *
 *            }
 *        });
 *    thread.start();
 * </pre>
 *
 * <br>
 * NOTE: In case that you add at least one listener to a launcher no exception
 * is thrown when a solver produces an error. The exceptions of the solvers are
 * stored within the solver object and can be accessed by
 * <code>solver.getException</code>.
 */

public class SolverLauncher implements SolverListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(SolverLauncher.class);

    /**
     * {@link ExecutorService} for {@link SMTSolver} callables.
     * Variable is initialized on first construction of {@link SolverLaunchers}
     */
    @Nonnull
    private static ExecutorService executorService;

    /**
     * A session encapsulates some attributes that should be accessed only by
     * specified methods (in order to maintain thread safety)
     */
    private final Session session = new Session();

    /**
     * The SMT settings that should be used
     */
    private final SMTSettings settings;

    private final List<SolverLauncherListener> listeners = new LinkedList<>();

    /**
     * Every launcher object should be used only once.
     */
    private boolean launcherHasBeenUsed = false;

    private final Map<SMTProblem, List<Future<SMTSolverResult>>> submittedTasks =
            new HashMap<>();

    /**
     * Create for every solver execution a new object. Don't reuse the solver
     * launcher object.
     *
     * @param settings settings for the execution of the SMT Solvers.
     */
    public SolverLauncher(SMTSettings settings) {
        this.settings = settings;
        if (executorService == null) {
            executorService = Executors.newFixedThreadPool(settings.getMaxConcurrentProcesses(),
                    new DefaultDaemonThreadFactory());
        }
    }

    /**
     * Adds a listener to the launcher object. The listener can be used to
     * observe the solver execution. If at least one listener was added to the
     * solver launcher, no exception is thrown when a solver produces an error.
     * The error can be read when the method <code>launcherStopped</code> of the
     * listener is called.
     */
    public void addListener(SolverLauncherListener listener) {
        listeners.add(listener);
    }

    public void removeListener(SolverLauncherListener listener) {
        listeners.remove(listener);
    }

    /**
     * Launches several solvers for the problem that is handed over.<br>
     * Note: Calling this methods does not create an extra thread, i.e. the
     * calling thread is blocked until the method returns. (Synchronous method
     * call).
     *
     * @param problem     The problem that should be translated and passed to the
     *                    solvers
     * @param services    The services object of the current proof.
     * @param solverTypes A list of solver types that should be used for the problem.
     */
    public void launch(SMTProblem problem, Services services, SolverType... solverTypes) {
        checkLaunchCall();
        LOGGER.info("Launch SMT solvers ({} solvers, {} problem)", solverTypes, problem);
        launchIntern(problem, solverTypes, services);
    }

    /**
     * Launches several solvers for the problems that are handed over. Note:
     * Calling this methods does not create an extra thread, i.e. the calling
     * thread is blocked until the method returns. (Synchronous method call).
     *
     * @param problems    The problems that should be translated and passed to the
     *                    solvers
     * @param services    The services object of the current proof.
     * @param solverTypes A list of solver types that should be used for the problem.
     */
    public void launch(Collection<SolverType> solverTypes,
                       Collection<SMTProblem> problems, Services services) {
        checkLaunchCall();
        launchIntern(solverTypes, problems, services);
    }

    /**
     * Stops the execution of all previously submitted {@link SMTSolver} task.
     */
    public void stop(ReasonOfInterruption reason) {
        synchronized (submittedTasks) { //can only be called from a different than the thread that called launch"
            submittedTasks.forEach((k, v) -> {
                for (Future<SMTSolverResult> submittedTask : v) {
                    submittedTask.cancel(true);
                }
            });
            session.interruptAll(reason);
        }
    }


    /**
     * Creates the concrete solver objects and distributes them to the SMT
     * problems.
     */
    private void prepareSolvers(Collection<SolverType> factories,
                                Collection<SMTProblem> problems, Services services) {
        for (SMTProblem problem : problems) {
            for (SolverType factory : factories) {
                if (factory.isInstalled(false)) {
                    SMTSolver solver = factory.createSolver(problem, this, services);
                    solver.setTimeout(settings.getTimeout(factory));
                    problem.addSolver(solver);
                }
            }
        }
    }

    private void launchIntern(SMTProblem problem, SolverType[] solverTypes, Services services) {
        var types = Arrays.asList(solverTypes);
        var problems = new ArrayList<SMTProblem>();
        problems.add(problem);
        launchIntern(types, problems, services);
    }

    private void launchIntern(Collection<SolverType> factories,
                              Collection<SMTProblem> problems, Services services) {
        // consider only installed solvers.
        var installedSolvers = new ArrayList<SolverType>(factories.size());
        for (SolverType type : factories) {
            if (type.isInstalled(false)) {
                installedSolvers.add(type);
                if (settings.checkForSupport()) {
                    type.checkForSupport();
                }
            }
        }
        prepareSolvers(installedSolvers, problems, services);
        launchIntern(problems, installedSolvers);
    }

    private void checkLaunchCall() {
        if (launcherHasBeenUsed) {
            throw new IllegalStateException("Every launcher object can be used only once.");
        }
        launcherHasBeenUsed = true;
    }

    private void launchIntern(Collection<SMTProblem> problems, Collection<SolverType> factories) {
        var solvers = new ArrayList<SMTSolver>(problems.size() * factories.size());
        for (SMTProblem problem : problems) {
            solvers.addAll(problem.getSolvers());
        }
        launchSolvers(solvers, problems, factories);
    }

    private void launchSolvers(List<SMTSolver> solvers,
                               Collection<SMTProblem> problems, Collection<SolverType> solverTypes) {
        //Show progress dialog
        notifyListenersOfStart(problems, solverTypes);

        // sorting by timeout to maintain a increasing waiting time list
        solvers.sort(Comparator.comparing(SMTSolver::getTimeout));

        // callback to cancelCallback all known solvers on the same sub-problem
        Consumer<SMTProblem> cancelCallback = smtProblem -> {
            synchronized (submittedTasks) {
                if (submittedTasks.containsKey(smtProblem)) {
                    smtProblem.getSolvers().forEach(it -> it.interrupt(ReasonOfInterruption.LOSER));
                    submittedTasks.get(smtProblem).forEach(it -> {
                        try {
                            it.cancel(true);
                        } catch (CompletionException ignore) {
                            //ignore: Task is already finished. No actions needed.
                        }
                    });
                }
            }
        };

        var futures = new ArrayList<Future<SMTSolverResult>>();
        synchronized (submittedTasks) {
            for (var it : solvers) {
                final var future = executorService.submit(createSolverTask(it, cancelCallback));
                submittedTasks.computeIfAbsent(it.getProblem(), k -> new ArrayList<>(4)).add(future);
                futures.add(future);
            }
        }

        for (int i = 0; i < solvers.size(); i++) {
            long currentTimeout = solvers.get(i).getTimeout();
            final var startTime = solvers.get(i).getStartTime();
            long waitTime = currentTimeout +
                    startTime < 0 ? 0 /* not started, just wait the timeout */
                    : Math.min(0, startTime) - System.currentTimeMillis(); // time wasted between start and get() call.
            var future = futures.get(i);
            try {
                future.get(waitTime, TimeUnit.MILLISECONDS);
            } catch (InterruptedException e) {
                LOGGER.warn("Waiting for termination of SMTSolver got interrupted. Cancel all submitted tasks!", e);
                stop(ReasonOfInterruption.TIMEOUT);
                Thread.currentThread().interrupt();
            } catch (ExecutionException e) {
                LOGGER.warn("Exception during the execution of an SMTSolver", e);
                solvers.get(i).interrupt(ReasonOfInterruption.EXCEPTION);
            } catch (TimeoutException e) {
                LOGGER.warn("Timout ({} ms) hit by SMTSolver. SMTSolver will be killed.", currentTimeout);
                future.cancel(true);
                solvers.get(i).interrupt(ReasonOfInterruption.TIMEOUT);
            } catch (CancellationException e) {
                LOGGER.info("SMT solver was cancelled while we wait on termination.");
            }
        }

        // kill remaining tasks!
        for (var entries : submittedTasks.entrySet()) {
            for (var submittedTask : entries.getValue()) {
                submittedTask.cancel(true);
            }
        }

        for (SMTSolver solver : solvers) {
            solver.interrupt(ReasonOfInterruption.USER);
        }

        notifyListenersOfStop();
    }

    private void notifyListenersOfStart(Collection<SMTProblem> problems, Collection<SolverType> solverTypes) {
        for (SolverLauncherListener listener : listeners) {
            listener.launcherStarted(problems, solverTypes, this);
        }
    }

    private Callable<SMTSolverResult> createSolverTask(SMTSolver solver, Consumer<SMTProblem> cancel) {
        return () -> {
            session.addCurrentlyRunning(solver);
            solver.setSettings(settings);
            LOGGER.info("launch SMT solver {}, (t/o: {})", solver.getType().getInfo(), solver.getTimeout());
            var res = solver.call();
            session.removeCurrentlyRunning(solver);
            session.addFinishedSolver(solver);
            if (res.isValid() != SMTSolverResult.ThreeValuedTruth.UNKNOWN) {
                cancel.accept(solver.getProblem());
            }
            return res;
        };
    }


    private void notifyListenersOfStop() {
        Collection<SMTSolver> problemSolvers = session.getProblemSolvers();
        Collection<SMTSolver> finishedSolvers = session.getFinishedSolvers();

        for (SMTSolver solver : problemSolvers) {
            if (!finishedSolvers.contains(solver)) {
                finishedSolvers.add(solver);
            }
        }

        for (SolverLauncherListener listener : listeners) {
            listener.launcherStopped(this, finishedSolvers);
        }

        if (!problemSolvers.isEmpty() && listeners.isEmpty()) {
            throw new SolverException(problemSolvers);
        }
    }

    /**
     * Is called when a solver has finished its task (Solver Thread). It removes
     * the solver from the list of the currently running solvers and tries to
     * wake up the launcher.
     */
    private void notifySolverHasFinished(SMTSolver solver) {
        session.removeCurrentlyRunning(solver);
    }

    @Override
    public void processStarted(SMTSolver solver, SMTProblem problem) {
    }

    @Override
    public void processStopped(SMTSolver solver, SMTProblem problem) {
        session.addFinishedSolver(solver);
        notifySolverHasFinished(solver);
    }

    @Override
    public void processInterrupted(SMTSolver solver, SMTProblem problem,
                                   Throwable e) {
        session.addProblemSolver(solver);
        notifySolverHasFinished(solver);
    }

    @Override
    public void processTimeout(SMTSolver solver, SMTProblem problem) {
        notifySolverHasFinished(solver);
    }

    @Override
    public void processUser(SMTSolver solver, SMTProblem problem) {
    }

}

/**
 * The session class encapsulates some attributes that should be only accessed
 * by specified methods (in order to maintain thread safety)
 */
class Session {
    private final Collection<SMTSolver> finishedSolvers = new ArrayList<>(16);
    private final Collection<SMTSolver> problemSolvers = new ArrayList<>(16);
    private final List<SMTSolver> currentlyRunning = new ArrayList<>(16);

    /**
     * Adds a solver to the list of currently running solvers. Thread safe
     */
    public void addCurrentlyRunning(SMTSolver solver) {
        synchronized (currentlyRunning) {
            currentlyRunning.add(solver);
        }
    }

    public void removeCurrentlyRunning(SMTSolver solver) {
        synchronized (currentlyRunning) {
            currentlyRunning.remove(solver);
        }
    }

    public int getCurrentlyRunningCount() {
        synchronized (currentlyRunning) {
            return currentlyRunning.size();
        }
    }

    public void interruptSolver(SMTSolver solver, ReasonOfInterruption reason) {
        solver.interrupt(reason);
        removeCurrentlyRunning(solver);
    }

    public void interruptAll(ReasonOfInterruption reason) {
        synchronized (currentlyRunning) {
            for (SMTSolver solver : currentlyRunning) {
                solver.interrupt(reason);
            }
        }
    }

    public void addProblemSolver(SMTSolver solver) {
        synchronized (problemSolvers) {
            problemSolvers.add(solver);
        }
    }

    public void addFinishedSolver(SMTSolver solver) {
        synchronized (finishedSolvers) {
            finishedSolvers.add(solver);
        }
    }

    public Collection<SMTSolver> getProblemSolvers() {
        synchronized (problemSolvers) {
            return new ArrayList<>(problemSolvers);
        }
    }

    public Collection<SMTSolver> getFinishedSolvers() {
        synchronized (finishedSolvers) {
            return new ArrayList<>(finishedSolvers);
        }
    }

}

/**
 * An adoption of the original {@link java.util.concurrent.Executors.DefaultThreadFactory} for creating daemon threads.
 * Using this thread factory in {@link ExecutorService} does prevent them from blocking regular termination by
 * reaching the end of main entry point.
 */
class DefaultDaemonThreadFactory implements ThreadFactory {
    private static final AtomicInteger poolNumber = new AtomicInteger(1);
    private final ThreadGroup group;
    private final AtomicInteger threadNumber = new AtomicInteger(1);
    private final String namePrefix;

    DefaultDaemonThreadFactory() {
        SecurityManager s = System.getSecurityManager();
        group = (s != null) ? s.getThreadGroup() : Thread.currentThread().getThreadGroup();
        namePrefix = "solver-launcher-pool-" + poolNumber.getAndIncrement() + "-thread-";
    }

    public Thread newThread(@Nonnull Runnable r) {
        Thread t = new Thread(group, r, namePrefix + threadNumber.getAndIncrement(), 0);
        t.setDaemon(true);
        if (t.getPriority() != Thread.NORM_PRIORITY)
            t.setPriority(Thread.NORM_PRIORITY);
        return t;
    }
}