package org.key_project.citool;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import de.uka.ilkd.key.TestSuite;
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
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.stream.Stream;

public class Main {

    public static class Arguments {
        @Parameter// option("--xml-output").file()
        File junitXmlOutput;

        @Parameter(names = "--measuring",
                description = "try to measure proof coverage")
        boolean enableMeasuring = false;

        @Parameter(description = "defines additional key files to be included",
                names = "--includes")
        List<String> includes;

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
        List<File> classpath;

        @Parameter(names = {"--bootClassPath", "-bcp"}, description = "set the bootclasspath")
        File bootClassPath;

        @Parameter(names = "--contract", description = "whitelist contracts by their names")
        List<String> onlyContracts;


        @Parameter(names = "--forbid-contact",
                description = "forbid contracts by their name")
        List<String> forbidContracts;

        @Parameter(description = "key, java or a folder")
        List<File> inputFile;

        @Parameter(names = "--proof-path", description = "folders to look for proofs and script files")
        List<File> proofPath;

    }

    public static void main(String[] args) throws IOException {
        printm("KeY version: ${KeYConstants.VERSION}");
        printm("KeY internal: ${KeYConstants.INTERNAL_VERSION}");
        printm("Copyright: ${KeYConstants.COPYRIGHT}");
        printm("More information at: https://formal.iti.kit.edu/weigl/ci-tool/");

        Arguments arguments = new Arguments();
        JCommander.newBuilder()
                .addObject(arguments)
                .build()
                .parse(args);

        Checker checker = new Checker(arguments);
        checker.run();
    }
}

class Checker {
    public static final char ESC = (char) 27;
    public static final int RED = 31;
    public static final int GREEN = 32;
    public static final int YELLOW = 33;
    public static final int BLUE = 34;
    public static final int MAGENTA = 35;
    public static final int CYAN = 36;

    final Main.Arguments args;
    private ChoiceSettings choiceSettings;
    private int currentPrintLevel = 0;

    Checker(Main.Arguments args) {
        this.args = args;
    }

    public static String color(Object s, int c) {
        //TODO
        return "${ESC}[${c}m$s${ESC}[0m";
    }


    private void initEnvironment() throws ProblemLoaderException {
        if (!ProofSettings.isChoiceSettingInitialised()) {
            var env = KeYEnvironment.load(new File("."), null, null, null);
            env.dispose();
        }
        choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
    }


    void printBlock(String message) {
        printm(message);
        currentPrintLevel++;
        f.invoke();
        currentPrintLevel--;
    }

    private void printm(String message, int fg) {
        System.out.print("  ".repeat(currentPrintLevel));
        System.out.println(color(message, fg));
    }

    private void printf(String message, Object... args) {
        System.out.print("  ".repeat(currentPrintLevel));
        System.out.format(message, args);
    }

    private void printm(String message) {
        System.out.print("  ".repeat(currentPrintLevel));
        System.out.println(message);
    }

    private int errors = 0;
    private TestSuite testSuites = new TestSuite();

    public void run() throws IOException {
        testSuites.name = args.inputFile.joinToString(" ");
        args.inputFile.forEach(it -> run(it));
        if (args.junitXmlOutput != null) {
            try (var it = new BufferedWriter(new FileWriter(args.junitXmlOutput))) {
                testSuites.writeXml(it);
            }
        }
        System.exit(errors);
    }

    private void run(String inputFile) {
        printBlock("[INFO] Start with `$inputFile`") {
            var pm = KeYApi.loadProof(new File(inputFile),
                    classpath.map {
                new File(it);
            },
            bootClassPath ?.let {
                new File(it);
            },
            includes.map {
                new File(it);
            })

            var contracts = pm.proofContracts
                    .filter {
                it.name in onlyContracts || onlyContracts.isEmpty()
            }

            printm("[INFO] Found: ${contracts.size}")
            var successful = 0;
            var ignored = 0;
            var failure = 0;

            val testSuite = testSuites.newTestSuite(inputFile);
            ProofSettings.DEFAULT_SETTINGS.properties.forEach({
                    (t, u) ->
                            testSuite.properties[t.toString()] = u;
            });

            for (var c : contracts) {
                var testCase = testSuite.newTestCase(c.name);
                printBlock("[INFO] Contract: `${c.name}`") {
                    var filename = MiscTools.toValidFileName(c.name);
                    when {
                        c.name in forbidContracts -> {
                            printm(" [INFO] Contract excluded by `--forbid-contract`")
                            testCase.result = TestCaseKind.Skipped("Contract excluded by `--forbid-contract`.")
                            ignored++;
                        }
                        dryRun -> {
                            printm("[INFO] Contract skipped by `--dry-run`")
                            testCase.result = TestCaseKind.Skipped("Contract skipped by `--dry-run`.")
                            ignored++
                        }
                        else ->{
                            var b = runContract(pm, c, filename);
                            if (b) {
                                //testCase.result = TestCaseKind.Skipped("Contract excluded by `--forbid-contract`.")
                                successful++;
                            } else {
                                testCase.result = JUnit.TestCaseKind.Failure("Proof not closeable.");
                                failure++;
                            }
                        }
                    }
                }
            }
            printm("[INFO] Summary for $inputFile: " +
                    "(successful/ignored/failure) " +
                    "(${color(successful, GREEN)}/${color(ignored, BLUE)}/${color(failure, RED)})")
            if (failure != 0)
                printm("[ERR ] $inputFile failed!", fg = RED)
        }
    }

    private Boolean runContract(ProofManagementApi pm, Contract c, String filename) throws ProofInputException, ProblemLoaderException {
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
                printm("[FINE] ${proof.openGoals().size()} remains open");
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
        var script = new File(scriptFile).readText();
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
                    getPathToRoot(it).forEach(it -> {
                                var p = it.getNodeInfo().getActiveStatement() ?.positionInfo
                                if (p != null) {
                                    visitLineOnClosedGoals.add(p.fileName to p.startPosition.line)
                                }
                            }
                    );
            printm("Visited lines:\n${visitLineOnClosedGoals.joinToString("\n")}");
        }
    }

    private List<String> proofFileCandidates;

    public List<String> getProofFileCandidates() {
        if (proofFileCandidates == null) {
            proofFileCandidates = new ArrayList<>();
            args.proofPath.forEach(it ->
                    proofFileCandidates.addAll(new File(it).list())
            );
        }
        return proofFileCandidates;
    }

    private String findProofFile(String filename) {
        return proofFileCandidates.stream().filter(it ->
                it.startsWith(filename) && (it.endsWith(".proof") || it.endsWith(".proof.gz"))
        ).findFirst().orElse(null);
    }

    private String findScriptFile(String filename) {
        return proofFileCandidates.stream().filter(it ->
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

    private static Pair<Integer, Integer> openClosedProgramBranches(Proof self) {
        List<Node> branchingNodes = new LinkedList<>();
        self.root().subtreeIterator().forEachRemaining(
                it -> {
                    if (it.childrenCount() > 1) {
                        branchingNodes.add(it);
                    }
                });
        var programBranchingNodes = branchingNodes.stream().filter(
                it -> {
                    var childStmt = it.childrenIterator().asSequence().map {
                        child -> child.nodeInfo.activeStatement
                    }
                    childStmt.any {
                        c -> c != it.nodeInfo.activeStatement
                    }
                });

        var diverseProgramBranches = programBranchingNodes.stream().filter({
                parent ->
                        !parent.isClosed && parent.childrenIterator().asSequence().any{
                it.isClosed}
        });

        return new Pair<>(diverseProgramBranches.count(), programBranchingNodes.count());
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
