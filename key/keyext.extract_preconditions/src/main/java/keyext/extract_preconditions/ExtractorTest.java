package keyext.extract_preconditions;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.FullAutoPilotProofMacro;
import de.uka.ilkd.key.macros.HeapSimplificationMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.util.KeYTypeUtil;
import de.uka.ilkd.key.util.MiscTools;
import keyext.extract_preconditions.printers.JsonPreconditionPrinter;
import keyext.extract_preconditions.printers.PreconditionPrinter;
import keyext.extract_preconditions.printers.SimplePreconditionPrinter;
import keyext.extract_preconditions.projections.AbstractTermProjection;
import keyext.extract_preconditions.projections.LeaveOutProjection;
import keyext.extract_preconditions.projections.NoProjection;
import keyext.extract_preconditions.projections.SimpleProjection;
import keyext.extract_preconditions.strategies.ResolveIntermediateVariablesStrategy;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import java.awt.event.WindowAdapter;
import java.io.File;
import java.util.*;

/**
 * Class to try out precondition extraction.
 * Based on the Main Class in org.key_project.Main
 *
 * @author steuber
 */
public class ExtractorTest {
    private static final int MAX_STEPS = 50000;

    /**
     * Main method allowing the test of the precondition extraction funtionality
     *
     * @param args First parameter: JML file to load
     */
    public static void main(String[] args) {
        if (args.length <= 0) {
            System.err.println("No file provided");
            return;
        }
        String javaFileName = args[0];
        File location = new File(javaFileName);
        if (!location.exists()) {
            System.err.println("File not found: " + javaFileName);
            return;
        }
        List<File> classPaths = null; // Optionally: Additional specifications for API classes
        File bootClassPath = null; // Optionally: Different default specifications for Java API
        List<File> includes = null; // Optionally: Additional includes to consider
        final KeYEnvironment<?> env;
        try {
            env = createKeyEnvironment(location, classPaths, bootClassPath, includes);
        } catch (ProblemLoaderException e) {
            System.err.println("Failed loading file in KeY:");
            e.printStackTrace();
            return;
        }
        ImmutableList<ProgramVariable> projectionVars = null;
        if (args.length>=2) {
            Iterator<String> argsIterator = Arrays.stream(args).iterator();
            // Skip file name
            argsIterator.next();
            projectionVars = ImmutableSLList.nil();
            while (argsIterator.hasNext()) {
                projectionVars = projectionVars.append(
                    new LocationVariable(new ProgramElementName(argsIterator.next()), Sort.ANY)
                );
            }
        }

        List<UnclosedProof> unclosedProofs = generateProofs(env,
                                                            location.getPath().endsWith("proof"),
                                                            projectionVars);

        boolean openWindow = getYesNo("Inspect proofs in KeY? (y/n)");

        if (openWindow) {
            MainWindow mainWindow = MainWindow.getInstance();
            AbstractMediatorUserInterfaceControl visualUi = mainWindow.getUserInterface();
            for (UnclosedProof currentUnclosed : unclosedProofs) {
                visualUi.registerProofAggregate(new SingleProof(
                    currentUnclosed.proof,
                    currentUnclosed.proof.name().toString()));
            }
            mainWindow.removeWindowListener(mainWindow.getExitMainAction().windowListener);
            mainWindow.addWindowListener(new WindowAdapter() {
                @Override
                public void windowClosing(java.awt.event.WindowEvent e) {
                    mainWindow.setVisible(false);
                    List<UnclosedProof> finalUnclosedProofs = new LinkedList<>();
                    for (UnclosedProof curProof : unclosedProofs) {
                        if (!curProof.proof.isDisposed()) {
                            finalUnclosedProofs.add(curProof);
                        }
                    }
                    extractPreconditions(finalUnclosedProofs, env);
                    System.exit(0);
                }
            });
        } else {
            extractPreconditions(unclosedProofs, env);
        }
    }

    public static boolean getYesNo(String msg) {
        Scanner kbd = new Scanner (System.in);
        boolean yn = false;
        boolean res = false;
        while (!yn) {
            System.out.println(msg);
            switch (kbd.nextLine()) {
                case "y":
                case "yes":
                    res = true;
                    yn = true;
                    break;
                case "n":
                case "no":
                    res = false;
                    yn = true;
                    break;
                default:
                    break;
            }
        }
        return res;
    }

    private static void extractPreconditions(List<UnclosedProof> unclosedProofs, KeYEnvironment<?> env) {
        UserInterfaceControl ui = env.getUi();
        try {
            for (UnclosedProof currentUnclosed : unclosedProofs) {
                Proof currentProof = currentUnclosed.proof;
                Set<Name> blackList = new HashSet<>();
                //blackList.add(new Name("self"));
                //blackList.add(new Name("heap"));
                AbstractTermProjection projection = new SimpleProjection(currentProof.getServices());
                    //new NoProjection(currentProof.getServices());
                    /*new LeaveOutProjection(currentUnclosed.programVariables,
                        currentProof.getServices(),
                        true, blackList);*/
                //AbstractTermProjection projection = new NoProjection(currentProof.getServices());
                PreconditionExtractor preconditionExtractor =
                    new PreconditionExtractor(
                        currentProof,
                        ui,
                        projection
                    );
                ImmutableList<Term> preconditionList = preconditionExtractor.extract();
                System.out.println(
                    "Found precondition for " + currentProof.name() + ":");
                PreconditionPrinter printer = new JsonPreconditionPrinter(currentProof.getServices());
                printer.print(preconditionList);
                currentProof.dispose();
            }
        } catch (Exception exception) {
            exception.printStackTrace();
        } finally {
            if (env != null) {
                env.dispose();
            }
        }
    }

    /**
     * Generates all proofs for the given KeY environment.
     * Applies FullAutoPilotProofMacro on those proofs
     *
     * @param env KeY envirionment
     * @return List of all proofs with open goals
     */
    private static List<UnclosedProof> generateProofs(KeYEnvironment<?> env,
                                                      boolean loadProofFile,
                                                      ImmutableList<ProgramVariable> projectionVariablesList) {
        // TODO(steuber): We probably want to adjust this a little? Or make it configurable...
        List<UnclosedProof> unclosedProofs = new LinkedList<>();
        if (loadProofFile) {
            Proof curProof = env.getLoadedProof();
            if (!curProof.openGoals().isEmpty()) {
                unclosedProofs.add(
                    new UnclosedProof(curProof, projectionVariablesList)
                );
            }
            return unclosedProofs;
        } else {
            // List all specifications of all types in the source location (not classPaths and bootClassPath)
            final List<Contract> proofContracts = new LinkedList<>();
            Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
            for (KeYJavaType type : kjts) {
                if (!KeYTypeUtil.isLibraryClass(type)) {
                    ImmutableSet<IObserverFunction> targets =
                        env.getSpecificationRepository().getContractTargets(type);
                    for (IObserverFunction target : targets) {
                        ImmutableSet<Contract> contracts =
                            env.getSpecificationRepository().getContracts(type, target);
                        for (Contract contract : contracts) {
                            proofContracts.add(contract);
                        }
                    }
                }
            }
            // Perform proofs
            for (Contract contract : proofContracts) {
                Proof proof = null;
                try {
                    // Create proof
                    proof =
                        env.createProof(contract.createProofObl(env.getInitConfig(), contract));
                    // Set proof strategy options
                    StrategyProperties sp =
                        proof.getSettings().getStrategySettings().getActiveStrategyProperties();
                    sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
                        StrategyProperties.METHOD_CONTRACT);
                    sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY,
                        StrategyProperties.DEP_ON);
                    sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                        StrategyProperties.QUERY_ON);
                    sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
                        StrategyProperties.NON_LIN_ARITH_DEF_OPS);
                    sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY,
                        StrategyProperties.STOPMODE_NONCLOSE);
                    proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
                    // Make sure that the new options are used
                    int maxSteps = MAX_STEPS;
                    ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
                    ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                        .setActiveStrategyProperties(sp);
                    proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
                    //AbstractProofMacro autopilot = new FullAutoPilotProofMacro();
                    //autopilot.applyTo(env.getUi(), proof.root(), null, null);
                    proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
                    // Start auto mode
                    env.getUi().getProofControl().startAndWaitForAutoMode(proof);
                    AbstractProofMacro closeProvable = new TryCloseMacro();
                    // Close Closables
                    closeProvable.applyTo(env.getUi(), proof.root(), null, null);
                    // Simplify heaps
                    HeapSimplificationMacro heapSimplifier = new HeapSimplificationMacro();
                    heapSimplifier.applyTo(env.getUi(), proof.root(), null, null);
                    // Resolve Variables through ApplyEqReverse
                    proof.setActiveStrategy(new ResolveIntermediateVariablesStrategy());
                    env.getUi().getProofControl().startAndWaitForAutoMode(proof);
                    // Simplify heaps again
                    heapSimplifier.applyTo(env.getUi(), proof.root(), null, null);
                    // Close Closables
                    closeProvable.applyTo(env.getUi(), proof.root(), null, null);
                    // Show proof result
                    boolean closed = proof.openGoals().isEmpty();
                    if (!closed) {
                        if (projectionVariablesList != null) {
                            unclosedProofs.add(
                                new UnclosedProof(proof, projectionVariablesList)
                            );
                        } else {
                            unclosedProofs.add(
                                new UnclosedProof(proof, contract.getOrigVars().params)
                            );
                        }
                    }
                } catch (ProofInputException e) {
                    System.out.println("Exception at '" + contract.getDisplayName() + "' of " +
                        contract.getTarget() + ":");
                    e.printStackTrace();
                } catch (Exception e) {
                    e.printStackTrace();
                } finally {
                    if (proof != null && proof.openGoals().isEmpty()) {
                        proof
                            .dispose(); // Ensure always that all instances of Proof are disposed
                    }
                }
            }
        }
        return unclosedProofs;
    }

    /**
     * Creates a KeY environment loading the given file
     *
     * @param location Input File
     * @return A new KeY environment
     * @throws ProblemLoaderException FIle could not be loaded
     */
    private static KeYEnvironment<?> createKeyEnvironment(File location, List<File> classPaths,
                                                          File bootClassPath, List<File> includes)
        throws ProblemLoaderException {
        // Ensure that Taclets are parsed
        if (!ProofSettings.isChoiceSettingInitialised()) {
            System.out.println("Trying to load "+location.getAbsolutePath());
            KeYEnvironment<?>
                env = KeYEnvironment.load(location, classPaths, bootClassPath, includes);

            env.dispose();
        }
        // Set Taclet options
        ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
        HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
        HashMap<String, String> newSettings = new HashMap<>(oldSettings);
        newSettings.putAll(MiscTools.getDefaultTacletOptions());
        choiceSettings.setDefaultChoices(newSettings);
        // Load source code
        return KeYEnvironment.load(location, classPaths, bootClassPath,
            includes);
    }
}

class UnclosedProof {
    public final Proof proof;
    public ImmutableList<Name> programVariables;

    public UnclosedProof(Proof proof,
                         ImmutableList<ProgramVariable> programVariables) {
        this.proof = proof;
        this.programVariables = ImmutableSLList.nil();
        for (ProgramVariable var : programVariables) {
            this.programVariables = this.programVariables.append(var.name());
        }
    }
}