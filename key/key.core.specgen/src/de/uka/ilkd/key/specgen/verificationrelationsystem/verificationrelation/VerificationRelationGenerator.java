package de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.key_project.util.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;

public class VerificationRelationGenerator {

	private Services myServices;
	private TermBuilder myTermBuilder;
	
	private static VerificationRelationGenerator instance = null;

	private VerificationRelationGenerator() {}

	public static VerificationRelationGenerator getInstance() {
		if (instance == null) {
			instance = new VerificationRelationGenerator();
		}
		return instance;
	}

	public Set<VerificationRelation> generate(Sequent sequent, Services services) {
		myServices = services;
		myTermBuilder = services.getTermBuilder();
		Set<VerificationRelation> verificationRelations = new HashSet<>();
		normalize(sequent);
		return verificationRelations;
	}

	public void normalize(Sequent sequent) {
		// assert normal form
		ImmutableList<SequentFormula> antecedentSequentFormulas = sequent.antecedent().asList();
		ImmutableList<SequentFormula> succedentSequentFormulas = sequent.succedent().asList();
		for (SequentFormula currentAntecedentSequentFormula : antecedentSequentFormulas) {
			assert (!currentAntecedentSequentFormula.formula().containsJavaBlockRecursive());
		}
		for (SequentFormula currentSuccedentSequentFormula : succedentSequentFormulas) {
			assert (currentSuccedentSequentFormula.formula().containsJavaBlockRecursive());
		}
		assert (succedentSequentFormulas.size() == 1);
		Term succedent = succedentSequentFormulas.head().formula();
		Term update = succedent.sub(0);
		StatementBlock program = ((StatementBlock) succedent.sub(1).javaBlock().program()).getInnerMostMethodFrame()
				.getBody();
		Term postcondition = succedent.sub(1).sub(0);
		Placeholder placeholder = generatePlaceholder(update);
		Term instance = placeholder.getInstance();
	}
	
	public Placeholder generatePlaceholder(Term update) {
		UpdateProgramVariableCollector pvCollector = new UpdateProgramVariableCollector();
		pvCollector.visit(update);
		Set<LocationVariable> pvSet = pvCollector.result();
		List<LocationVariable> pvList = new ArrayList<>(pvSet);
		Placeholder placeholder = new Placeholder("I", pvList, myTermBuilder);
		return placeholder;
	}
	
	
/*
	public void analyze() {
		final ProgramMethod method = findMethod();
		final StatementBlock mBody = method.getBody();

		final SymbExInterface seIf = new SymbExInterface(file, env);
		final Proof initialProof = seIf.initProof(method);

		this.services = initialProof.getServices();
		final MethodFrame origMF;
		final ImmutableArray<Branch> tryBranches;

		{
			final ApplyStrategyInfo getMethodFrameProofResult = MergeRuleUtils.tryToProve(
					initialProof.root().sequent().succedent().getFirst().formula(), initialProof.getServices(), true,
					"UpToLoop", 5000);

			// XXX: Dirty approach with *a lot* of assumptions about the proof /
			// formula structure

			final Optional<Goal> maybeGoalWithMF = getMethodFrameProofResult.getProof().openGoals().stream()
					.filter(g -> g.sequent().succedent().asList().stream()
							.anyMatch(sf -> sf.formula().containsJavaBlockRecursive()))
					.findAny();

			assert maybeGoalWithMF.isPresent() : "Could not find a goal with a method frame";

			ImmutableList<SequentFormula> getMFGoalSucc = maybeGoalWithMF.get().sequent().succedent().asList();
			origMF = JavaTools.getInnermostMethodFrame(TermBuilder
					.goBelowUpdates(getMFGoalSucc.take(getMFGoalSucc.size() - 1).head().formula()).javaBlock(),
					initialProof.getServices());
			tryBranches = ((Try) ((StatementBlock) TermBuilder
					.goBelowUpdates(getMFGoalSucc.take(getMFGoalSucc.size() - 1).head().formula()).javaBlock()
					.program()).getFirstElement()).getBranchList();
		}

		final Term pre = initialProof.root().sequent().succedent().getFirst().formula().sub(0);
		final Term update = initialProof.root().sequent().succedent().getFirst().formula().sub(1).sub(0);
		final Term post = initialProof.root().sequent().succedent().getFirst().formula().sub(1).sub(1).sub(0);

		// 0: Locate While loop
		While whileStatement = null;
		{
			for (int i = 0; i < mBody.getBody().size(); i++) {
				Statement currentStatement = mBody.getStatementAt(i);
				if (currentStatement instanceof While) {
					whileStatement = (While) currentStatement;
					break;
				}
			}
		}

		// 1: Create program up to while loop
		final StatementBlock progBeforeWhile;
		final LoopSpecification inv;
		int i = 0;
		{
			final ArrayList<ProgramElement> stmntBeforeWhile = new ArrayList<ProgramElement>();
			for (; i < mBody.getBody().size(); i++) {
				final Statement stmt = mBody.getStatementAt(i);
				if (stmt instanceof LoopStatement) {
					break;
				}

				stmntBeforeWhile.add(stmt);
			}

			assert i < mBody.getChildCount()
					&& mBody.getStatementAt(i) instanceof LoopStatement : "No while loop found";
			final LoopStatement loop = (LoopStatement) mBody.getStatementAt(i);
			inv = env.getServices().getSpecificationRepository().getLoopSpec(loop);

			progBeforeWhile = new StatementBlock(stmntBeforeWhile.toArray(new Statement[stmntBeforeWhile.size()]));
		}

		// 2: Create program after while loop
		final Statement progAfterWhile;
		{
			final ArrayList<ProgramElement> stmntAfterWhile = new ArrayList<ProgramElement>();
			i++;
			for (; i < mBody.getBody().size(); i++) {
				final Statement stmt = mBody.getStatementAt(i);
				assert !(stmt instanceof While) : "Only one loop supported";

				stmntAfterWhile.add(stmt);
			}

			progAfterWhile = KeYJavaASTFactory.tryBlock(
					new MethodFrame(origMF.getProgramVariable(), origMF.getExecutionContext(),
							new StatementBlock(stmntAfterWhile.toArray(new Statement[stmntAfterWhile.size()]))),
					tryBranches.toArray(new Branch[0]));
		}

		// 3: Execute program before with precondition, extract updated
		// precondition
		Term tUpToLoopResult = null;
		{
			final ProgramVariableCollector pvCollect = new ProgramVariableCollector(progBeforeWhile, env.getServices());
			pvCollect.start();
			final Set<LocationVariable> pvsBeforeLoop = pvCollect.result();
			pvsBeforeLoop
					.addAll(MergeRuleUtils.getUpdateLeftSideLocations(update).stream().collect(Collectors.toSet()));

			final Function p = new Function(new Name("p"), Sort.FORMULA,
					pvsBeforeLoop.stream().map(pv -> pv.sort()).collect(Collectors.toList()).toArray(new Sort[0]));
			final Term pTerm = tb.func(p,
					pvsBeforeLoop.stream().map(pv -> tb.var(pv)).collect(Collectors.toList()).toArray(new Term[0]));

			final Term tUpToLoop = tb.imp(pre,
					tb.apply(update, tb.prog(Modality.BOX, JavaBlock.createJavaBlock(progBeforeWhile), pTerm)));

			final ApplyStrategyInfo upToLoopResult = MergeRuleUtils.tryToProve(tUpToLoop, initialProof.getServices(),
					true, "UpToLoop", 5000);

			tUpToLoopResult = extractAnalysisResultFromProofTree(tb, p, pTerm, upToLoopResult.getProof());
		}

		// TODO: Create anonymizing update for afterLoop part, as
		// in loop scope inv rule, just without inv.

		// 4: Execute program after, extract weakest precondition
		Term tAfterLoopResult = null;
		{
			final Term tUpToLoop = tb.apply(update,
					tb.prog(Modality.BOX, JavaBlock.createJavaBlock(new StatementBlock(progAfterWhile)), post));

			final ProofEnvironment sideProofEnv = SideProofUtil
					.cloneProofEnvironmentWithOwnOneStepSimplifier(initialProof);

			ProofStarter proofStarter = null;
			try {
				proofStarter = SideProofUtil.createSideProof(sideProofEnv,
						Sequent.createSuccSequent(new Semisequent(new SequentFormula(tUpToLoop))), "UpToLoop");
			} catch (ProofInputException e) {
				e.printStackTrace();
				System.exit(1);
			}

			ProofMacroFinishedInfo finishedInfo = null;
			try {
				finishedInfo = new FinishSymbolicExecutionMacro().applyTo(seIf.keyEnvironment().getUi(),
						proofStarter.getProof().root(), null, seIf.keyEnvironment().getUi());
			} catch (Exception e) {
				e.printStackTrace();
				System.exit(1);
			}

			final Proof sideProof = finishedInfo.getProof();
			final BuiltInRule OSS = sideProof.getInitConfig().builtInRules().stream()
					.filter(r -> r instanceof OneStepSimplifier).findAny().get();
			for (Goal g : sideProof.openGoals()) {
				for (SequentFormula sf : g.sequent().succedent()) {
					g.apply(OSS.createApp(new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
							sideProof.getServices()));
				}
			}
		}
	}
*/
}
