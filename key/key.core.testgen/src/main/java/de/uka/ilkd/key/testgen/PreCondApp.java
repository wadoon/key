package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.api.KeYApi;
import de.uka.ilkd.key.api.ProofApi;
import de.uka.ilkd.key.api.ProofManagementApi;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.macros.TestGenMacro;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.settings.TestGenerationSettings;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.testgen.BaseTestGenerator;
import de.uka.ilkd.key.smt.testgen.PrintStreamLog;
import de.uka.ilkd.key.smt.testgen.StopRequest;
import de.uka.ilkd.key.smt.testgen.TestGenerationLog;
import de.uka.ilkd.key.speclang.Contract;

import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (12/12/20)
 */
public class PreCondApp {
    static final PrintStream err = System.err;
    static final PrintStream out = System.out;

    public static void main(String[] args) throws ProblemLoaderException, InterruptedException, ProofInputException {
        String[] arguments = args;
        if (args.length <= 0) {
            err.println("Invalid parameter number.");
            arguments = new String[]{
                    "/home/weigl/Documents/qarch/casestudies/AgeOfMajority/KeY/Maturity.java", "run", "get"
            };
        }

        err.format("Load file: %s%n", arguments[0]);
        ProofManagementApi api = KeYApi.loadProof(new File(arguments[0]));
        List<Contract> contracts = api.getProofContracts();
        err.format("Found %d contracts%n", contracts.size());
        for (Contract contract : contracts) {
            err.format("Use contract: %s", contract.getDisplayName());
            ProofApi papi = api.startProof(contract);
            Proof proof = papi.getProof();
            KeYEnvironment<?> env = papi.getEnv();
            for (int i = 1; i < arguments.length; i++) {
                err.format("Execute command: %s%n", arguments[i]);
                switch (arguments[i]) {
                    case "run":
                        executeMacro(proof, env.getUi());
                        break;
                    case "get":
                        get(proof, env.getUi());
                        break;
                }
            }

        }
    }


    private static void get(Proof proof, UserInterfaceControl ui) {
        BaseTestGenerator tg = new BaseTestGenerator(ui, proof);
        try {
            TestGenerationLog log = new PrintStreamLog(err);
            StopRequest stopRequest = () -> false;
            List<Proof> proofs = tg.createProofsForTesting(true, true);

            List<SMTProblem> smt = proofs.stream()
                    .flatMap(it -> tg.blastProof(stopRequest, log, it).stream())
                    .collect(Collectors.toList());

            TestGenerationSettings settings = tg.getTestGenerationSettings();
            final ProofIndependentSMTSettings piSettings = tg.getProofIndependentSMTSettings(settings);
            final ProofDependentSMTSettings pdSettings = tg.getProofDependentSMTSettings(settings, proof);
            // invoke z3 for counterexamples
            final SMTSettings smtsettings = new SMTSettings(pdSettings, piSettings, proof);
            run(smt, smtsettings, proof);
            for (SMTProblem problem : smt) {
                if(problem.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE) {
                    //System.out.println(problem.getTerm());
                    System.out.println(LogicPrinter.quickPrintTerm(problem.getTerm(), proof.getServices()));
                }
            }
        } finally {
            tg.dispose();
        }
    }

    private static void run(List<SMTProblem> smt, SMTSettings smtsettings, Proof proof) {
        SolverLauncher launcher = new SolverLauncher(smtsettings);
        launcher.addListener(new SolverLauncherListener() {
            @Override
            public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers) {
            }

            @Override
            public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes, SolverLauncher launcher) {
            }
        });

        final List<SolverType> solvers = new ArrayList<>();
        solvers.add(SolverType.Z3_CE_SOLVER);
        SolverType.Z3_CE_SOLVER.checkForSupport();
        launcher.launch(solvers, smt, proof.getServices());
    }

    private static void executeMacro(Proof proof, UserInterfaceControl ui) throws InterruptedException {
        err.format("Applying TestGen Macro (bounded symbolic execution)...");
        TestGenMacro macro = new TestGenMacro();
        macro.applyTo(ui, proof, proof.openEnabledGoals(), null, null);
        err.println("Finished symbolic execution.");
    }
}

