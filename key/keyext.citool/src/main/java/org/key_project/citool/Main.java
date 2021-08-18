package org.key_project.citool;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.*;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import org.key_project.citool.JUnit.TestCaseKind;
import org.key_project.citool.JUnit.TestSuites;
import org.key_project.util.collection.ImmutableList;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import static org.key_project.citool.Printer.*;

public class Main {
    public static class Arguments {
        @Parameter(names = "--xml-output")
        File junitXmlOutput;

        @Parameter(names = "--measuring",
                description = "try to measure proof coverage")
        boolean enableMeasuring = false;

        @Parameter(description = "defines additional key files to be included",
                names = "--includes")
        List<File> includes;

        @Parameter(names = "--auto-mode-max-step",
                description = "maximal amount of steps in auto-mode [default:10000]")
        int autoModeStep = 10000;

        @Parameter(names = {"-v", "--verbose"}, description = "verbose output, currently unused")
        boolean verbose = false;

        @Parameter(names = "--dry-run",
                description = "skipping the proof reloading, scripts execution and auto mode." +
                        " Useful for finding the contract names")
        boolean dryRun = false;

        @Parameter(names = {"--classpath", "-cp"}, description = "additional classpaths")
        List<File> classpath = new ArrayList<>();

        @Parameter(names = {"--bootClassPath", "-bcp"}, description = "set the bootclasspath")
        File bootClassPath;

        @Parameter(names = "--contract", description = "whitelist contracts by their names")
        List<String> onlyContracts = new ArrayList<>();


        @Parameter(names = "--forbid-contact",
                description = "forbid contracts by their name")
        List<String> forbidContracts = new ArrayList<>();

        @Parameter(description = "key, java or a folder")
        List<File> inputFile = new ArrayList<>();

        @Parameter(names = "--proof-path", description = "folders to look for proofs and script files")
        List<File> proofPath = new ArrayList<>();

    }

    public static void main(String[] args) throws IOException {
        printf("KeY version: %s", KeYConstants.VERSION);
        printf("KeY internal: %s", KeYConstants.INTERNAL_VERSION);
        printf("KeY Copyright: %s", KeYConstants.COPYRIGHT);
        printf("More information at: https://formal.iti.kit.edu/weigl/ci-tool/");

        Arguments arguments = new Arguments();
        JCommander.newBuilder()
                .addObject(arguments)
                .build()
                .parse(args);

        Checker checker = new Checker(arguments);
        checker.run();
    }
}

class Printer {
    private static int currentPrintLevel = 0;
    public static final char ESC = (char) 27;

    public static String color(Object s, int c) {
        return ESC + "[" + c + "m" + s + ESC + "[0m";
    }

    public static void printBlock(String message, Runnable obj) {
        printm(message);
        currentPrintLevel++;
        obj.run();
        currentPrintLevel--;
    }

    public static void printm(String message, int fg) {
        System.out.print("  ".repeat(currentPrintLevel));
        System.out.println(color(message, fg));
    }

    public static void printf(String message, Object... args) {
        System.out.print("  ".repeat(currentPrintLevel));
        System.out.format(message, args);
        System.out.println();
    }

    public static void printm(String message) {
        System.out.print("  ".repeat(currentPrintLevel));
        System.out.println(message);
    }

    public static void inc() {
        currentPrintLevel++;
    }

    public static void dec() {
        currentPrintLevel--;
    }

    public static void printerr(String msg, Object... args) {
        System.err.format(msg, args);
        System.err.println();
    }
}

class Checker {
    public static final int RED = 31;
    public static final int GREEN = 32;
    public static final int YELLOW = 33;
    public static final int BLUE = 34;
    public static final int MAGENTA = 35;
    public static final int CYAN = 36;

    final Main.Arguments args;
    private ChoiceSettings choiceSettings;

    Checker(Main.Arguments args) {
        this.args = args;
    }


    private void initEnvironment() throws ProblemLoaderException {
        if (!ProofSettings.isChoiceSettingInitialised()) {
            var env = KeYEnvironment.load(new File("."), null, null, null);
            env.dispose();
        }
        choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
    }


    private int errors = 0;
    private final TestSuites testSuites = new TestSuites();

    public void run() throws IOException {
        if (args.inputFile == null || args.inputFile.isEmpty()) {
            printerr("No input files given");
            System.exit(1);
        }

        testSuites.name = args.inputFile.stream()
                .map(File::getName)
                .collect(Collectors.joining(" "));
        for (File file : args.inputFile) {
            try {
                run(file.getAbsoluteFile());
            } catch (ProofInputException | ProblemLoaderException e) {
                e.printStackTrace();
                System.exit(-1);
            }
        }
        if (args.junitXmlOutput != null) {
            try (var it = new BufferedWriter(new FileWriter(args.junitXmlOutput))) {
                testSuites.writeXml(new JUnit.XmlWriter(it));
            }
        }
        System.exit(errors);
    }

    private void run(File inputFile) throws ProofInputException, ProblemLoaderException {
        printf("[INFO] Start with `%s`", inputFile);
        Printer.inc();
        var pm = KeYApi.loadProof(
                inputFile,
                args.classpath,
                args.bootClassPath,
                args.includes);

        var contracts = pm.getProofContracts().stream()
                .filter(it -> args.onlyContracts.contains(it.getName()) || args.onlyContracts.isEmpty())
                .collect(Collectors.toList());

        printf("[INFO] Found: %s", contracts.size());
        var successful = 0;
        var ignored = 0;
        var failure = 0;
        var error = 0;

        var testSuite = testSuites.newTestSuite(inputFile.toString());
        ProofSettings.DEFAULT_SETTINGS.getProperties().forEach((t, u) ->
                testSuite.properties.put(t.toString(), u));

        for (var c : contracts) {
            var testCase = testSuite.newTestCase(c.getName());
            printf("[INFO] Contract: %s", c.getName());
            Printer.inc();
            var filename = MiscTools.toValidFileName(c.getName());
            if (args.forbidContracts.contains(c.getName())) {
                printm(" [INFO] Contract excluded by `--forbid-contract`");
                testCase.result = new TestCaseKind.Skipped("Contract excluded by `--forbid-contract`.");
                ++ignored;
            } else if (args.dryRun) {
                printm("[INFO] Contract skipped by `--dry-run`");
                testCase.result = new TestCaseKind.Skipped("Contract skipped by `--dry-run`.");
                ++ignored;
            } else {
                Boolean b = null;
                try {
                    b = runContract(pm, c, filename);
                    if (b) {
                        successful++;
                    } else {
                        testCase.result = new JUnit.TestCaseKind.Failure("Proof not closeable.", null);
                        failure++;
                    }
                } catch (Exception e) {
                    e.printStackTrace();
                    error++;
                }
            }
            Printer.dec();
        }

        Printer.dec();
        printf("[INFO] Summary for %s: " +
                        "(successful/ignored/failure/error) " +
                        "(%s/%s/%s/%s)",
                inputFile, color(successful, GREEN), color(ignored, BLUE),
                color(failure, RED), color(error, YELLOW));
        if (failure != 0 || error != 0) {
            printm("[ERR ] " + inputFile + " failed!", RED);
        }
    }


    private Boolean runContract(ProofManagementApi pm, Contract c, String filename) throws ProofInputException, ProblemLoaderException, ScriptException, IOException, InterruptedException {
        var proofApi = pm.startProof(c);
        var proof = proofApi.getProof();
        assert (proof != null);

        proof.getSettings().getStrategySettings().setMaxSteps(args.autoModeStep);
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(args.autoModeStep);

        final var proofFile = findProofFile(filename);
        final var scriptFile = findScriptFile(filename);
        final var ui = (AbstractUserInterfaceControl) proofApi.getEnv().getUi();
        final var pc = (AbstractProofControl) proofApi.getEnv().getProofControl();

        boolean closed;

        if (proofFile != null) {
            printm("[INFO] Proof found: $proofFile. Try loading.");
            closed = loadProof(proofFile);
        } else if (scriptFile != null) {
            printm("[INFO] Script found: $scriptFile. Try proving.");
            closed = loadScript(ui, proof, scriptFile);
        } else {
            if (args.verbose)
                printm("[INFO] No proof or script found. Fallback to auto-mode.");
            closed = runAutoMode(pc, proof);
        }

        if (closed) {
            printm("[OK  ] ✔ Proof closed.", GREEN);
        } else {
            errors++;
            printm("[ERR ] ✘ Proof open.", RED);
            if (args.verbose) {
                printf("[FINE] %s remains open", proof.openGoals().size());
            }
        }
        proof.dispose();
        return closed;
    }

    private Boolean runAutoMode(AbstractProofControl proofControl, Proof proof) {
        var startTime = System.currentTimeMillis();
        if (args.enableMeasuring) {
            var mm = new MeasuringMacro();
            proofControl.runMacro(proof.root(), mm, null);
            proofControl.waitWhileAutoMode();
            printm("[INFO] Proof has open/closed before: ${mm.before}");
            printm("[INFO] Proof has open/closed after: ${mm.after}");
        } else {
            proofControl.startAndWaitForAutoMode(proof);
        }
        var stopTime = System.currentTimeMillis();
        var time = stopTime - startTime / 1000.0;
        if (args.verbose) {
            printf("[FINE] Auto-mode took %d seconds.", time);
        }
        printStatistics(proof);
        return proof.closed();
    }

    private boolean loadScript(AbstractUserInterfaceControl ui, Proof proof, String scriptFile) throws IOException, ScriptException, InterruptedException {
        var script = Files.readString(Paths.get(scriptFile));
        var engine = new ProofScriptEngine(script, new Location(scriptFile, 1, 1));
        var startTime = System.currentTimeMillis();
        engine.execute(ui, proof);
        var stopTime = System.currentTimeMillis();
        var time = stopTime - startTime / 1000.0;
        printf("Script execution took %.3f seconds.", time);
        printStatistics(proof);
        return proof.closed();
    }

    private boolean loadProof(String keyFile) throws ProblemLoaderException {
        var env = KeYEnvironment.load(new File(keyFile));
        try {
            var proof = env.getLoadedProof();
            try {
                if (proof == null) {
                    printm("[ERR] No proof found in given KeY-file.", 38);
                    return false;
                }
                printStatistics(proof);
                return proof.closed();
            } finally {
                if (proof != null) {
                    proof.dispose();
                }
            }
        } finally {
            env.dispose();
        }
    }


    private void printStatistics(Proof proof) {
        if (args.verbose) {
            proof.getStatistics().getSummary().forEach(
                    p -> printm("[FINE] ${p.first} = ${p.second}"));
        }

        if (args.enableMeasuring) {
            var closedGoals = proof.getClosedSubtreeGoals(proof.root());
            var visitLineOnClosedGoals = new HashSet<Pair<String, Integer>>();
            closedGoals.forEach(it ->
                    it.node().iterateToRoot().forEach(n -> {
                                var p = n.getNodeInfo().getActiveStatement().getPositionInfo();
                                if (p != null) {
                                    visitLineOnClosedGoals.add(
                                            new Pair<>(p.getFileName(), p.getStartPosition().getLine()));
                                }
                            }
                    ));
            printf("Visited lines:\n%s",
                    visitLineOnClosedGoals.stream().map(Object::toString).collect(Collectors.joining()));
        }
    }

    private List<File> proofFileCandidates;

    public List<File> getProofFileCandidates() {
        if (proofFileCandidates == null) {
            proofFileCandidates = args.proofPath.stream()
                    .flatMap(it -> {
                        try {
                            return Files.walk(it.toPath());
                        } catch (IOException e) {
                            e.printStackTrace();
                            return null;
                        }
                    })
                    .filter(Objects::nonNull)
                    .map(Path::toFile)
                    .filter(it -> it.getName().endsWith(".proof"))
                    .collect(Collectors.toList());

            printf("Found %d proof files", proofFileCandidates.size());
        }
        return proofFileCandidates;
    }

    private String findProofFile(String filename) {
        return getProofFileCandidates().stream().filter(it ->
                it.startsWith(filename) && (it.endsWith(".proof") || it.endsWith(".proof.gz"))
        ).findFirst().orElse(null);
    }

    private String findScriptFile(String filename) {
        return getProofFileCandidates().stream().filter(it ->
                it.startsWith(filename) && (it.endsWith(".txt") || it.endsWith(".pscript"))
        ).findFirst().orElse(null);
    }


    private Stream<Node> pathToRoot(Goal self) {
        List<Node> path = new ArrayList<>(64);
        Node cur = self.node();
        do {
            path.add(cur);
            cur = cur.parent();
        } while (cur != null);
        return path.stream();
    }

    private static Pair<Long, Long> openClosedProgramBranches(Proof self) {
        List<Node> branchingNodes = new LinkedList<>();
        self.root().subtreeIterator().forEachRemaining(
                it -> {
                    if (it.childrenCount() > 1) {
                        branchingNodes.add(it);
                    }
                });
        var programBranchingNodes = branchingNodes.stream().filter(
                it -> {
                    final Spliterator<Node> spliterator = Spliterators.spliteratorUnknownSize(it.childrenIterator(),
                            Spliterator.ORDERED);
                    var s = StreamSupport.stream(spliterator, false);
                    var childStmt = s.map(child -> child.getNodeInfo().getActiveStatement())
                            .filter(c -> c != it.getNodeInfo().getActiveStatement())
                            .findAny();
                    return childStmt.isPresent();
                });

        var diverseProgramBranches = programBranchingNodes.filter(parent ->
                !parent.isClosed() && parent.childrenStream().filter(it -> it.isClosed()).findAny().isPresent()
        );

        var p = new Pair<>(diverseProgramBranches.count(), programBranchingNodes.count());
        return p;
    }


    //region Measuring
    class MeasuringMacro extends SequentialProofMacro {
        Stats before = new Stats();
        Stats after = new Stats();

        @Override
        public String getName() {
            return "MeasuringMacro";
        }

        @Override
        public String getCategory() {
            return "ci-only";
        }

        @Override
        public String getDescription() {
            return "like auto but with more swag";
        }

        @Override
        public ProofMacro[] createProofMacroArray() {
            return new ProofMacro[]{
                    new AutoPilotPrepareProofMacro(),
                    new GatherStatistics(before),
                    new AutoMacro(), //or TryCloseMacro()?
                    new GatherStatistics(after)
            };
        }
    }

    class Stats {
        private int openGoals = 0;
        private int closedGoals = 0;

        public Stats() {
        }

        public Stats(int openGoals, int closedGoals) {
            this.openGoals = openGoals;
            this.closedGoals = closedGoals;
        }

        public int getOpenGoals() {
            return openGoals;
        }

        public void setOpenGoals(int openGoals) {
            this.openGoals = openGoals;
        }

        public int getClosedGoals() {
            return closedGoals;
        }

        public void setClosedGoals(int closedGoals) {
            this.closedGoals = closedGoals;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Stats)) return false;
            Stats stats = (Stats) o;
            return getOpenGoals() == stats.getOpenGoals() && getClosedGoals() == stats.getClosedGoals();
        }

        @Override
        public int hashCode() {
            return Objects.hash(getOpenGoals(), getClosedGoals());
        }
    }

    class GatherStatistics extends SkipMacro {
        private final Stats stats;

        GatherStatistics(Stats stats) {
            this.stats = stats;
        }

        @Override
        public String getName() {
            return "gather-stats";
        }

        @Override
        public String getCategory() {
            return "ci-only";
        }

        @Override
        public String getDescription() {
            return "stat purpose";
        }

        @Override
        public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals,
                                  PosInOccurrence posInOcc) {
            return true;
        }

        @Override
        public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                              Proof proof,
                                              ImmutableList<Goal> goals,
                                              PosInOccurrence posInOcc,
                                              ProverTaskListener listener) throws InterruptedException {
            // do nothing
            stats.setOpenGoals(proof.openGoals().size());
            stats.setClosedGoals(proof.getClosedSubtreeGoals(proof.root()).size());
            return super.applyTo(uic, proof, goals, posInOcc, listener);
        }
    }
//endregion
}
