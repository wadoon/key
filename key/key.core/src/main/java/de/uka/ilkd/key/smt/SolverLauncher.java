package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;
import java.util.stream.Collectors;

/**
 * IN ORDER TO START THE SOLVERS USE THIS CLASS.<br>
 * There are two cases how the solvers can be started:<br>
 * <br>
 * 1. Case: Starting the solvers synchronously<br>
 * <br>
 * First Step: Create the SMT problem:<br>
 * <code>SMTProblem problem = new SMTProblem(g); // g can be either a goal or term</code> <br>
 * <br>
 * Second Step: Create the launcher object:<br>
 * <code>SolverLauncher launcher = new SolverLauncher(new SMTSettings(){...});</code> <br>
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
 *          	// do something with the results here...
 *          	problem.getFinalResult();
 *          	// handling the problems that have occurred:
 *          	for(SMTSolver solver : problemSolvers){
 *          		solver.getException();
 *          		...
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
 * NOTE: In case that you add at least one listener to a launcher no exception is thrown when a
 * solver produces an error. The exceptions of the solvers are stored within the solver object and
 * can be accessed by <code>solver.getException</code>.
 */

public class SolverLauncher implements SolverListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(SolverLauncher.class);

    /**
     * The timer that is responsible for the timeouts.
     */
    private final Timer timer = new Timer(true);
    /**
     * A sesion encapsulates some attributes that should be accessed only by specified methods (in
     * oder to maintain thread safety)
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

    private static final ExecutorService executorService = Executors.newFixedThreadPool(2);

    private final List<Future<SMTSolverResult>> submittedTasks = new ArrayList<>();

    /**
     * Create for every solver execution a new object. Don't reuse the solver launcher object.
     *
     * @param settings settings for the execution of the SMT Solvers.
     */
    public SolverLauncher(SMTSettings settings) {
        this.settings = settings;
    }

    /**
     * Adds a listener to the launcher object. The listener can be used to observe the solver
     * execution. If at least one listener was added to the solver launcher, no exception is thrown
     * when a solver produces an error. The error can be read when the method
     * <code>launcherStopped</code> of the listener is called.
     */
    public void addListener(SolverLauncherListener listener) {
        listeners.add(listener);
    }

    public void removeListener(SolverLauncherListener listener) {
        listeners.remove(listener);
    }

    /**
     * Launches several solvers for the problem that is handed over.<br>
     * Note: Calling this methods does not create an extra thread, i.e. the calling thread is
     * blocked until the method returns. (Synchronous method call).
     *
     * @param problem The problem that should be translated and passed to the solvers
     * @param services The services object of the current proof.
     * @param solverTypes A list of solver types that should be used for the problem.
     */
    public void launch(SMTProblem problem, Services services, SolverType... solverTypes) {
        checkLaunchCall();
        try {
            launchIntern(problem, services, solverTypes);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Launches several solvers for the problems that are handed over. Note: Calling this methods
     * does not create an extra thread, i.e. the calling thread is blocked until the method returns.
     * (Synchronous method call).
     *
     * @param problems The problems that should be translated and passed to the solvers
     * @param services The services object of the current proof.
     * @param solverTypes A list of solver types that should be used for the problem.
     */
    public void launch(Collection<SolverType> solverTypes, Collection<SMTProblem> problems,
                       Services services) {
        checkLaunchCall();
        try {
            launchIntern(solverTypes, problems, services);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Stops the execution of the launcher.
     */
    public void stop() {
        for (Future<SMTSolverResult> submittedTask : submittedTasks) {
            submittedTask.cancel(true);
        }
        session.interruptAll(ReasonOfInterruption.USER);
    }

    /**
     * Creates the concrete solver objects and distributes them to the SMT problems.
     */
    private void prepareSolvers(Collection<SolverType> factories, Collection<SMTProblem> problems,
            Services services) {
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

    private void launchIntern(SMTProblem problem, Services services, SolverType[] solverTypes)
        throws InterruptedException {
        LinkedList<SolverType> types = new LinkedList<>();
        Collections.addAll(types, solverTypes);
        LinkedList<SMTProblem> problems = new LinkedList<>();
        problems.add(problem);
        launchIntern(types, problems, services);
    }

    private void launchIntern(Collection<SolverType> factories, Collection<SMTProblem> problems,
            Services services) throws InterruptedException {
        // consider only installed solvers.
        LinkedList<SolverType> installedSolvers = new LinkedList<>();
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

    private void launchIntern(Collection<SMTProblem> problems, Collection<SolverType> factories)
        throws InterruptedException {

        LinkedList<SMTSolver> solvers = new LinkedList<>();
        for (SMTProblem problem : problems) {
            solvers.addAll(problem.getSolvers());
        }
        launchSolvers(solvers, problems, factories);
    }

    private void launchSolvers(List<SMTSolver> solvers, Collection<SMTProblem> problems,
            Collection<SolverType> solverTypes) throws InterruptedException {
        // Show progress dialog
        notifyListenersOfStart(problems, solverTypes);

        solvers.sort(Comparator.comparing(SMTSolver::getTimeout));

        List<Future<SMTSolverResult>> futures = solvers.stream().map(it -> executorService.submit(createSolverTask(it)))
                .collect(Collectors.toList());
        submittedTasks.addAll(futures);

        for (int i = 0; i < solvers.size(); i++) {
            final long currentTimeout = solvers.get(i).getTimeout();
            final var startTime = solvers.get(i).getStartTime();

            var future = futures.get(i);
            try {
                long waitTime = currentTimeout + (startTime < 0 ? 0 : (startTime - System.currentTimeMillis()));
                future.get(waitTime, TimeUnit.MILLISECONDS);
            } catch (InterruptedException | ExecutionException e) {
                LOGGER.warn("Exception during the execution of an SMTSolver", e);
                future.cancel(true);
                solvers.get(i).interrupt(ReasonOfInterruption.EXCEPTION);
            } catch (TimeoutException e) {
                LOGGER.warn("Timeout ("+currentTimeout+" ms) hit by SMTSolver. SMTSolver will be killed.", e);
                future.cancel(true);
                solvers.get(i).interrupt(ReasonOfInterruption.TIMEOUT);
            } catch (CancellationException e) {
                LOGGER.warn("Cancellation of SMTSolver. SMTSolver will be killed.", e);
                future.cancel(true);
                solvers.get(i).interrupt(ReasonOfInterruption.EXCEPTION);
            }
        }

        /*
        for (SMTSolver solver : solvers) {
            solver.interrupt(ReasonOfInterruption.USER);
        }*/

        notifyListenersOfStop();

    }

    private Callable<SMTSolverResult> createSolverTask(SMTSolver solver) {
        return () -> {
            session.addCurrentlyRunning(solver);
            solver.setSettings(settings);
            var res = solver.call();
            session.removeCurrentlyRunning(solver);
            session.addFinishedSolver(solver);
            return res;
        };
    }

    private void notifyListenersOfStart(Collection<SMTProblem> problems,
            Collection<SolverType> solverTypes) {
        for (SolverLauncherListener listener : listeners) {
            listener.launcherStarted(problems, solverTypes, this);
        }
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
     * Is called when a solver has finished its task (Solver Thread). It removes the solver from the
     * list of the currently running solvers and tries to wake up the launcher.
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
    public void processInterrupted(SMTSolver solver, SMTProblem problem, Throwable e) {
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
 * The session class encapsulates some attributes that should be only accessed by specified methods
 * (in order to maintain thread safety)
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
        try {
            solver.interrupt(reason);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        removeCurrentlyRunning(solver);
    }

    public void interruptAll(ReasonOfInterruption reason) {
        synchronized (currentlyRunning) {
            for (SMTSolver solver : currentlyRunning) {
                try {
                    solver.interrupt(reason);
                } catch (InterruptedException e) {
                    throw new RuntimeException(e);
                }
            }
        }
    }

    public void addProblemSolver(SMTSolver solver){
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
