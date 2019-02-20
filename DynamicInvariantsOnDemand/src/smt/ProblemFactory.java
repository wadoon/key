package smt;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.macros.TestGenMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.settings.TestGenerationSettings;
import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.testgen.MemoryTestGenerationLog;

public class ProblemFactory {

	public static void create(Proof proof) {
		applySymbolicExecution(proof);
		List<Proof> openGoalProofs = AuxiliaryFunctions.createProofsForTesting(proof);
		Collection<SMTProblem> problems = applySemanticBlasting(openGoalProofs);
		solveSMTProblems(problems, proof);
	}

	private static void applySymbolicExecution(Proof proof) {
		try {
			TestGenMacro macro = new TestGenMacro();
			ImmutableList<Goal> openEnabledGoals = proof.openEnabledGoals();
			macro.applyTo(null, proof, openEnabledGoals, null, null);
		} catch (Throwable e) {
			e.printStackTrace();
		}
	}

	private static Collection<SMTProblem> applySemanticBlasting(List<Proof> proofs) {
		final Collection<SMTProblem> problems = new LinkedList<SMTProblem>();
		try {
			for (final Proof proof : proofs) {
				final SemanticsBlastingMacro macro = new SemanticsBlastingMacro();
				ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
				try {
					synchronized (macro) {
						macro.applyTo(null, proof, proof.openEnabledGoals(), null, null);
					}
					problems.addAll(SMTProblem.createSMTProblems(proof));
				} catch (Exception e) {
					e.getStackTrace();
				}
			}
		} finally {
		}
		return problems;
	}

	private static void solveSMTProblems(Collection<SMTProblem> problems, Proof proof) {
		final ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings()
				.clone();
		TestGenerationSettings settings = ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings();
		piSettings.setMaxConcurrentProcesses(settings.getNumberOfProcesses());
		final ProofDependentSMTSettings pdSettings = proof.getSettings().getSMTSettings().clone();
		pdSettings.invariantForall = settings.invaraiantForAll();
		final SMTSettings smtsettings = new SMTSettings(pdSettings, piSettings, proof);
		SolverLauncher launcher = new SolverLauncher(smtsettings);
		launcher.addListener(new SolverLauncherListener() {
			@Override
			public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers) {
				handleLauncherStopped(launcher, finishedSolvers, proof);
			}

			@Override
			public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes,
					SolverLauncher launcher) {
			}
		});
		final List<SolverType> solvers = new LinkedList<SolverType>();
		solvers.add(SolverType.Z3_CE_SOLVER);
		SolverType.Z3_CE_SOLVER.checkForSupport();
		launcher.launch(solvers, problems, proof.getServices());
		// ModelGenerator mg = new ModelGenerator(proofs.get(0).root().sequent(), 3,
		// getMediator());
		// mg.launch();
		return;
	}

	private static void handleLauncherStopped(SolverLauncher launcher, Collection<SMTSolver> problemSolvers, Proof proof) {
		try {
			problemSolvers = filterSolverResultsAndShowSolverStatistics(problemSolvers);
			if (problemSolvers.size() > 0) {
				generateFiles(launcher, problemSolvers, proof);
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private static Collection<SMTSolver> filterSolverResultsAndShowSolverStatistics(
			Collection<SMTSolver> problemSolvers) {
		final Vector<SMTSolver> output = new Vector<SMTSolver>();
		for (final SMTSolver solver : problemSolvers) {
			try {
				final SMTSolverResult.ThreeValuedTruth res = solver.getFinalResult().isValid();
				if (res == SMTSolverResult.ThreeValuedTruth.UNKNOWN) {
					if (solver.getException() != null) {
						solver.getException().printStackTrace();
					}
				} else if (res == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE) {
					ModelExtractor me = solver.getSocket().getQuery();
					if (me != null) {
						final Model m = me.getModel();
						if (TestCaseGenerator.modelIsOK(m)) {
							output.add(solver);
						}
					}
				} else {
					System.out.println("Valid Model");
				}
			} catch (final Exception e) {
				e.printStackTrace();
			}
		}
		System.out.println("Valid Paths - Number of Generated Test Cases: " + output.size());
		return output;
	}

	private static void generateFiles(SolverLauncher launcher, Collection<SMTSolver> problemSolvers, Proof proof) throws Exception {
		final TestCaseGenerator testCaseGenerator = new TestCaseGenerator(proof);
		testCaseGenerator.setLogger(new MemoryTestGenerationLog());
		testCaseGenerator.generateJUnitTestSuite(problemSolvers);
	}

}
