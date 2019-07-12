package core;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.StringReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.key_project.util.collection.ImmutableList;

import api.key.KeYAPI;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.TestGenerationSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import geninstrument.GenInstrumentData;
import geninstrument.InstrumentGenerator;
import gentest.GenTestHelper;
import gentest.IGenTest;
import helperfunctions.HelperFunctions;
import helperfunctions.TermUpdateVisitor;
import prover.InvGenResult;
import prover.Invariant;
import prover.ProofResult;
import prover.ProofWrapper;
import prover.SequentWrapper;
import smt.AuxiliaryFunctions;
import smt.ProblemFactory;

public class Main {
	private static final boolean useGeneratedInvariant = true;
	
	private static final String benchmarksFile1 = "benchmarks/pow2/Pow2.java";
	private static final String benchmarksFile2 = "benchmarks/sdiv/SDiv.java";
	private static final String benchmarksFile3 = "benchmarks/cohendiv/CohenDiv.java";
	private static final String benchmarksFile4 = "benchmarks/plus/Plus.java";
	private static final String benchmarksFile5 = "benchmarks/square/Square.java";
	private static final String benchmarksFile6 = "benchmarks/times/Times.java";
	private static final String benchmarksFile7 = "benchmarks/timestwo/TimesTwo.java";
	private static final String benchmarksFile8 = "benchmarks/cohencu/Cohencu.java";
	private static final String benchmarksFile11 = "benchmarks/prod4br/Prod4br.java";
	// only Plus does not work
	private static final String useBenchmark = benchmarksFile5;
	
	private static final String digRelPath = "dig/dig/dig.py";
	
	//Mock Inv for Debug purposes
	static int mockCount = 0;
	static boolean mock = false;
	static int mockLoopNum = 1;
	//static String mockRawDIGInv = "[i - i_0 == 0, i_0*u_n - r_0 == 0, n - u_n == 0, j - r + r_0 == 0]";
	//static String mockRawDIGInv = "[q*y + r - x == 0]";
	static String mockRawDIGInv = "[]";
	//static String mockRawDIGInv = "[_x- x == 0, x*x - x*y - z == 0]";
	
	// --- TestGen Parameters ---
	// Potential amount of testcases / method calls for the function from which the traces should be obtained
	// Cohen inner: unwinds = 11, bound = 11 -> Working
	public static final int concurrentSMTProcesses = 8;
	public static final int startMaxLoopUnwinds = 10;
	public static int maxLoopUnwinds = startMaxLoopUnwinds;
	public static final int startSMTintBound = 6;
	public static int SMTintBound = startSMTintBound;
	public static final int incLoopUnwindsBy = 3;
	public static final int incSmtBoundBy = 1;
	
	// --- DIG Parameters ---
	// Polynomial Degree
	public static final int startPolDegree = 1;
	public static int polDegree = startPolDegree;
	public static final int incPolDegreeBy = 1;
	
	// goal stack for backtracking, implemented for future logic, currently the first loop goal is the only element
	public static LinkedList<Node> lastValidNodes = new LinkedList<Node>();
	// we need to restore the old user specified inequality invariants at backtracking
	public static LinkedList<Triple<LoopInvariantBuiltInRuleApp, Services, Term>> loopsWithSpecInequalityInv = new LinkedList<Triple<LoopInvariantBuiltInRuleApp, Services, Term>>();
	
	private static KeYAPI keyAPI;
	
	
	public static void main(String[] args) {
		final long startOverallTime = System.nanoTime();
		final long startKeYParseTime = System.nanoTime();
		System.out.println("--- Reading Benchmark: " + useBenchmark);
		keyAPI = new KeYAPI(useBenchmark);
		final long endKeYParseTime = System.nanoTime();
		final long KeYParseTimeMs = (endKeYParseTime - startKeYParseTime) / 1000000;
		System.out.println("KeYParseTimeMs: " + KeYParseTimeMs);
		
		ProofIndependentSMTSettings settSMT = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
		TestGenerationSettings settTG = ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings();
		settTG.setMaxUnwinds(maxLoopUnwinds);
		settSMT.intBound = SMTintBound;
		//Timeout 5000 sec
		settSMT.timeout = 50000000;
		settSMT.setMaxConcurrentProcesses(concurrentSMTProcesses);
		settTG.setConcurrentProcesses(concurrentSMTProcesses);
		
		List<Contract> proofContracts = keyAPI.getContracts();
		ProofResult result = null;
		for(Contract currentContract : proofContracts) {
			Proof currentProof = keyAPI.createProof(currentContract);
			result = attemptProve(currentProof);
		}
		if(result != null) System.out.println("Successfully closed proof.");
		final long endOverallTime = System.nanoTime();
		final long overallTimeMs = (endOverallTime - startOverallTime) / 1000000;
		System.out.println("overallTimeMs: " + overallTimeMs);
	}
	
	private static ProofResult attemptProve(Proof proof) {
		while(!keyAPI.isClosed(proof)) {
			// --- KeY - AutoPilot ---
			final long startKeYAutoTime = System.nanoTime();
			ImmutableList<Goal> openGoals = keyAPI.prove(proof);
			final long endKeYAutoTime = System.nanoTime();
			final long KeYAutoTimeMs = (endKeYAutoTime - startKeYAutoTime) / 1000000;
			System.out.println("KeYAutoTimeMs: " + KeYAutoTimeMs);
			
			//--- Check if Backtracking is needed ----
			if (isInMinOneGoalNoLoopContained(openGoals)) {
				System.out.println("---- Backtrack - Invalid Inv ----");
				// currently, always backtrack to the very first loop goal
				// & reset all loop invariants to the spec ones, since they
				// got overwritten by the potential invariants
				backtrack(proof, lastValidNodes.peek(), loopsWithSpecInequalityInv);
				
				//--- Strenghten Parameters to be more successful next time -----
				strenghtenParameters();
				
				//--- Call recursively -> retry with new parameters ---
				attemptProve(proof);
			}
			
			// --- else Generate Potential Invariant ---
			else {
				for(Goal currentGoal : openGoals) {
					// --- Get Sequent from Goal ---
					SequentWrapper currentSequent = keyAPI.getSequent(currentGoal);
					
					// --- Save Loop with User specified Inequality Invariant ---
					// get user given inequality invariant part
					While loop = currentSequent.getLoop();
					// we got a loop, else we would have backtracked
					assert(loop != null);
					
					Term suggestedInvariant = null;
					try {
						suggestedInvariant = keyAPI.getSuggestedInvariant(loop);
						// save the inequality invariant for the loop to restore it at backtracking
						addLoopWithSpecInvToList(loopsWithSpecInequalityInv, currentGoal, suggestedInvariant);
					} catch (Exception e1) {
						// TODO Auto-generated catch block
						e1.printStackTrace();
					}
					
					Pair<InvGenResult, Goal> result = null;
					
					// push first loop goal, we always backtrack there, since it is not possible to
					// know at which loop its applied invariant was invalid
					if (lastValidNodes.isEmpty())
						lastValidNodes.push(currentGoal.node());
					
					// --- Generate Potential Invariant & Filter Candidates ---
					try {
						final long startInvGenTime = System.nanoTime();
						result = attemptInvGen(currentGoal, currentSequent, proof, suggestedInvariant);
						final long endInvGenTime = System.nanoTime();
						final long InvGenTimeMs = (endInvGenTime - startInvGenTime) / 1000000;
						System.out.println("InvGenTimeMs: " + InvGenTimeMs);
					} catch (ProofInputException e) {
						e.printStackTrace();
					}
					
					// --- Backtrack, if no potential Invariant was found ---
					if (result == null) {
						System.out.println("---- Backtrack - No Inv found ----");
						backtrack(proof, lastValidNodes.peek(), loopsWithSpecInequalityInv);
						
						//--- Strenghten Parameters to be more successful next time -----
						strenghtenParameters();
					}
					// --- Else Apply Potential Invariant -> Create InitiallyValid, BodyPreserves, UseCase Goal ---
					else {
						Invariant invariant = (Invariant)result.first;
						keyAPI.applyInvariantRule(result.second, invariant, useGeneratedInvariant);
					}
					
					//--- Call recursively for each goal---
					attemptProve(proof);
				}
			}
		}
		// --- Proof closed ---
		return new ProofWrapper(proof); 
	}

	private static void strenghtenParameters() {
		// DIG: Increase pol. degree by 1
		polDegree += incPolDegreeBy;
		// TestGen: Generate more test cases and increase SMT Bound
		ProofIndependentSMTSettings settSMT = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings();
		TestGenerationSettings settTG = ProofIndependentSettings.DEFAULT_INSTANCE.getTestGenerationSettings();
		maxLoopUnwinds += incLoopUnwindsBy;
		SMTintBound += incSmtBoundBy;
		settTG.setMaxUnwinds(maxLoopUnwinds);
		settSMT.intBound = SMTintBound;
	}
	
	private static void backtrack(Proof proof, Node pruneToNode,
			LinkedList<Triple<LoopInvariantBuiltInRuleApp, Services, Term>> loopsWithSpecInequalityInv) {
		proof.pruneProof(pruneToNode);
		// reset the invariants of the loops to the user specified inequalities, since they were overwritten
		for (Triple<LoopInvariantBuiltInRuleApp, Services, Term> loopAndIneqInv : loopsWithSpecInequalityInv) {
			setNewLoopInvariantOverwriteOld(loopAndIneqInv.first, loopAndIneqInv.second ,loopAndIneqInv.third);
		}
	}

	private static void addLoopWithSpecInvToList(
			LinkedList<Triple<LoopInvariantBuiltInRuleApp, Services, Term>> loopsWithSpecInequalityInv,
			Goal loopGoal, Term suggestedInvariant) {
		
		Pair<LoopInvariantBuiltInRuleApp, Services> p = createLoopInvariantBuiltInRuleApp(loopGoal);
		LoopInvariantBuiltInRuleApp ruleApplication = p.first;
		Services services = p.second;
		
		loopsWithSpecInequalityInv.add(
				new Triple<LoopInvariantBuiltInRuleApp, Services, Term>(ruleApplication, services, suggestedInvariant));
		
	}

	private static boolean isInMinOneGoalNoLoopContained(ImmutableList<Goal> openGoals) {
		SequentWrapper goalSequent;
		for(Goal goal : openGoals) {
			goalSequent = keyAPI.getSequent(goal);
			// try to retrieve the loop of the goal sequent
			While loop = goalSequent.getLoop();
			
			// return true if no loop was found
			if (loop == null)
				return true;
		}
		
		// in every goal a loop was found
		return false;
	}

	public static Pair<InvGenResult, Goal> attemptInvGen(Goal currentGoal, SequentWrapper sequent, Proof proof, Term suggestedInvariant) throws ProofInputException {
		mockCount++;
		
		List<Term> gamma 		= sequent.getGamma();
		StatementBlock program 	= sequent.getProgram();
		Term phi 				= sequent.getPhi();
		While loop 				= sequent.getLoop();
		Term update				= sequent.getUpdate();
		
		if (loop == null) {
			// This should not happen, since we would already have backtracked otherwise
			throw new IllegalArgumentException("attemptInvGen got a sequent with no loop.");
		}
		Goal loopGoal = proof.openGoals().head();
		
		final long startInputVarsAndNSTime = System.nanoTime();
		//--- Extrahiere Input Variablen---
		// Parse Updates
		TermUpdateVisitor varAndAssignmentCollector = new TermUpdateVisitor();
		update.execPreOrder(varAndAssignmentCollector);
		// Parse Assignments, Extrahier u.A. Input Variablen -> Save Data in Singleton
		GenInstrumentData.getInstance().isInitialized = false;
		analyzeAndParseAssignments(varAndAssignmentCollector.assignmentsLHS_RHS, varAndAssignmentCollector.LHSVariables);
		GenInstrumentData.getInstance().isInitialized = true;
		System.out.println("inputVars: " + GenInstrumentData.getInstance().inputVars);
		System.out.println("allVarsInScope: " + GenInstrumentData.getInstance().allVars.toString());
		
		//--- SetUp TermBuilder, Services and Namespaces for Parsing Terms such as Invariants---
		DefaultTermParser dtp = new DefaultTermParser();
		// add update vars to namespace to be able to use the parser for those vars
	    TermBuilder tb = proof.getServices().getTermBuilder();
		Services services = proof.getServices();
		AbbrevMap abbr = (services.getProof() == null) ? null
                : services.getProof().abbreviations();
		// copy the global namespace in order to add local variables and symbols (goal local namespace) to it,
		// to parse invariants over local "functions" such as i_0
        NamespaceSet extendedNS = services.getNamespaces().copy();
        // somehow the design of KeY leads to this: the local variables declared before loop are not known to this point,
        // only in updates specified. Need to add those to namespace, else the parser throws a "do not know variable" Exc.
        // copiedNS.programVariables().add(varAndAssignmentCollector.LHSVariables);
        // currentGoal.getLocalNamespaces().functions().parent().elements()
        for (Function f : currentGoal.getLocalNamespaces().functions().allElements()) {
			extendedNS.functions().add(f);
		}
        for (IProgramVariable v : currentGoal.getLocalNamespaces().programVariables().allElements()) {
        	extendedNS.programVariables().add(v);
        }
        final long endInputVarsAndNSTime = System.nanoTime();
        final long InputVarsAndNSTimeMs = (endInputVarsAndNSTime - startInputVarsAndNSTime) / 1000000;
        System.out.println("InputVarsAndNSTimeMs: " + InputVarsAndNSTimeMs);
        
        //--- Generate Instrumented Java Code for recording Traces out of Sequent ---
		System.out.println("--- Start generating modified method with traces code");
		// Generate Program Code with Traces for dynamic execution
		String javaCode = InstrumentGenerator.generateInstrumentFromKeYFormat(loop);
		
		//--- Save Instrument - TracesMethod Java Code to Workspace .java file ---
		Path currentPath = Paths.get(System.getProperty("user.dir"));
		Path filePath = Paths.get(currentPath.toString(), "dynacode", "geninstrument", "GenInstrument.java");
		HelperFunctions.writeStringToFile(javaCode, filePath.toString());
		
		String rawDIGInvariants = null;
		if (! (mock && mockCount == mockLoopNum)) {
			final long testGenStartTime = System.nanoTime();
			//--- Generate TestCases using modified TestGen ---
			System.out.println("--- Start test generation, loopUnwinds: " + maxLoopUnwinds + " , SMTBound: " + SMTintBound);
			// save proof state since TestGen "destroys" the proof
			Node validProofState = loopGoal.node();
			Term uselessInv = null;
			try {
				uselessInv = tb.parseTerm("0=0");
			} catch (ParserException e1) {
				e1.printStackTrace();
			}
			Term oldLoopInv = null;
			if (suggestedInvariant != null)
				// delete invariant (the user given Ineq.) -> else the TestGen simplifies too much with the given ineq inv
				oldLoopInv = setNewLoopInvariantOverwriteOld(loopGoal, uselessInv);
			// start mod TestGen
			ProblemFactory.create(proof);
			// restore previous proof state, since TestGen messes with it
			proof.pruneProof(validProofState);
			// the loopGoal still broken, pruneProof created a new one
			loopGoal = proof.openGoals().head();
			// restore old inv (user given ineq)
			if (oldLoopInv != null) {
				setNewLoopInvariantOverwriteOld(loopGoal, oldLoopInv);
			}
			final long testGenEndTime = System.nanoTime();
	        final long testGenTimeMs = (testGenEndTime - testGenStartTime) / 1000000;
	        System.out.println("testGenTimeMs: " + testGenTimeMs);
	        
	        
			//--- Call Generated TestCases and Obtain Traces ---
	        final long callTestsStartTime = System.nanoTime();
			System.out.println("--- Call generated test / obtain traces..");
			IGenTest generatedTest = GenTestHelper.getGeneratedTest();
			HashMap<String, ArrayList<Integer>> varTraces = generatedTest.callGenTest();
			final long callTestsEndTime = System.nanoTime();
	        final long callTestsTimeMs = (callTestsEndTime - callTestsStartTime) / 1000000;
	        System.out.println("callTestsTimeMs: " + callTestsTimeMs);
			
			
			//--- Format Traces to DIG Format ---
			int numTraces = 0;
			if (varTraces.values().iterator().hasNext())
				numTraces = varTraces.values().iterator().next().size();
			System.out.println("Write " + numTraces + " traces in DIG format to file..");
			String tracesDIG = HelperFunctions.formatTracesToDIG(varTraces);
			
			
			//--- Write Traces to file in workspace ---
			Path tracesFilePath = Paths.get(currentPath.toString(), "traces.tcs");
			HelperFunctions.writeStringToFile(tracesDIG, tracesFilePath.toString());
			
			
			final long callDIGStartTime = System.nanoTime();
			//--- Call DIG with traces to get Invariants ---
			System.out.println("--- Call DIG with traces file to get Invariants, degree: " + polDegree);
			Path digAbsPath = Paths.get(currentPath.toString(), digRelPath);
			rawDIGInvariants = callDIGGetInvs(digAbsPath.toString(), tracesFilePath.toString(), true, polDegree);
			//String rawDIGIneq = callDIGGetInvs(digAbsPath.toString(), tracesFilePath.toString(), false);
			final long callDIGEndTime = System.nanoTime();
	        final long callDIGTimeMs = (callDIGEndTime - callDIGStartTime) / 1000000;
	        System.out.println("callDIGTimeMs: " + callDIGTimeMs);
		}
		
		if(mock && mockCount == mockLoopNum)
			rawDIGInvariants = mockRawDIGInv;
		System.out.println("Raw DIG Eq: " + rawDIGInvariants);
		
		//--- Parse DIG Invariant Array to String Array ----
		List<String> digInvariants = parseDIGInvariantArray(rawDIGInvariants);
		//List<String> digIneq = parseDIGInvariantArray(rawDIGIneq);
		
		//--- Convert DIG Invariants to KeY Parseable Format ----
		List<String> convertedInvariantStrings = convertDIGInvariantsToJMLFormat(digInvariants, true, false);
		//List<String> convertedIneqStrings = convertDIGInvariantsToJMLFormat(digIneq, true, false);
		System.out.println("JML Invs: " + convertedInvariantStrings);

		
        //--- Convert Invariant Strings to KeY Terms ---
		List<Term> invariantCandidateTerms = parseInvariantStringsAsTerm(convertedInvariantStrings, dtp, services, extendedNS, abbr);
		//List<Term> invariantIneqCandidateTerms = parseInvariantStringsAsTerm(convertedIneqStrings, dtp, services, existingNS, abbr);
		
		//--- Pre Filter for Initially Valid ---
		final long preFilterStartTime = System.nanoTime();
		
		List<Term> initValidCandidates = filterCandidatesInitiallyValid(invariantCandidateTerms, loopGoal);
		
		final long preFilterEndTime = System.nanoTime();
        final long preFilterTimeMs = (preFilterEndTime - preFilterStartTime) / 1000000;
        System.out.println("preFilterTimeMs: " + preFilterTimeMs);
		// care: old loop goal now broken, since we pruned proof in filterCandidatesInitiallyValid
		
		//--- To implement: Filter Candidates with Advanced Body Filter ---
		List<Term> bodyPreservesCandidates = filterCandidatesBodyPreserves(initValidCandidates);
		
		
		//--- Extract User Specified Inequality Invariant Terms ----
		List<String> inequalitiesStrings = extractInequalitiesFromTerm(suggestedInvariant);
		List<Term> inequalitiesTerms = parseInvariantStringsAsTerm(inequalitiesStrings, dtp, services, extendedNS, abbr);
		
		
		//--- If no Candidate is left, return null ---
		if (initValidCandidates.isEmpty()) {
			return null;
		}
		System.out.println("--- InitValid Candidates: " + initValidCandidates);
		
		//--- Build KeY Invariant Conjunction out of Candidates and specified inequalities ---
		Term conjInvariant = buildConjunction(initValidCandidates, inequalitiesTerms, tb);
		
		System.out.println("--- Full Inv-Term with User given Ineq: " + conjInvariant.toString());
		
		//return current openGoal, since prune proof modified the previous openGoal, a new one (similar) was created
		Goal openGoal = proof.openGoals().head();
		return new Pair<InvGenResult, Goal>(new Invariant(conjInvariant), openGoal);
	}
	
	private static Term buildConjunction(List<Term> candidates, List<Term> inequalityInvs, TermBuilder tb) {
		Term conjInvariant = null;
		for (Term candidate : candidates) {
			if (conjInvariant != null)
				conjInvariant = tb.and(conjInvariant, candidate);
			else
				conjInvariant = candidate;
		}
		for (Term ineq : inequalityInvs) {
				if (conjInvariant != null)
					conjInvariant = tb.and(conjInvariant, ineq);
				else
					conjInvariant = ineq;
		}
		
		return conjInvariant;
	}
	
	public static void analyzeAndParseAssignments(LinkedList<Pair<String, String>> assignmentsLHS_RHS, HashSet<LocationVariable> LHSVariables) {
		// Extrahiere input Variables vom visitor & build assignments
		LinkedHashSet<String> inputVars = new LinkedHashSet<String>(); // int _x = x
		LinkedHashSet<String> allVars = new LinkedHashSet<String>();
		LinkedHashSet<String> nonInputVars = new LinkedHashSet<String>();
		List<String> javaAssignments = new LinkedList<String>();
		
		StringBuilder assBuilder = new StringBuilder();
		for (Pair<String, String> e : assignmentsLHS_RHS) {
			String lhs = e.first;
			String rhs = e.second;;
			
			allVars.add(lhs);
			nonInputVars.add(lhs);
			
			// Build Assignments
			assBuilder.append("int ");
			assBuilder.append(lhs);
			assBuilder.append(" = ");
			assBuilder.append(rhs);
			assBuilder.append(";");
			
			javaAssignments.add(assBuilder.toString());
			assBuilder.setLength(0);
			
			// Right hand side must be on a Left hand side assignment, else it is an input Var
			if (!HelperFunctions.isInteger(rhs) && !LHSVariables.contains(rhs)) {
				inputVars.add(rhs);
				allVars.add(rhs);
			} 
		}
		
		//Save Information
		GenInstrumentData.getInstance().inputVars = inputVars;
		GenInstrumentData.getInstance().allVars = allVars;
		GenInstrumentData.getInstance().javaAssignments = javaAssignments;
		GenInstrumentData.getInstance().nonInputVars = nonInputVars;
	}

	private static List<Term> filterCandidatesBodyPreserves(List<Term> initValidCandidates) {
		// TODO Auto-generated method stub
		return null;
	}

	private static List<Term> filterCandidatesInitiallyValid(List<Term> invariantCandidateTerms, Goal loopGoal) {
		List<Term> initiallyValidCandidates = new LinkedList<Term>();
		Node prevState = loopGoal.node();
		Proof proof = loopGoal.proof();
		Goal openGoal = loopGoal;
		
		for(Term cand : invariantCandidateTerms) {
			//Pair<Term, ImmutableList<Goal>> oldInvAndGoalList = setNewLoopInvariantOverwriteOldAndApplyToCopy(loopGoal, cand);
			Pair<Term, ImmutableList<Goal>> oldInvAndGoalList = setNewLoopInvariantOverwriteOldAndApply(openGoal, cand);
			Term oldLoopInv = oldInvAndGoalList.first;
			final ImmutableList<Goal> goalList = oldInvAndGoalList.second;
			//}
			// { From WhileInvariantRule.apply
	        Goal initGoal = goalList.tail().tail().head();
	        Goal bodyGoal = goalList.tail().head();
	        Goal useGoal = goalList.head();
	        //}
			
	        boolean invInitiallyValid = false;
			ImmutableList<Goal> openGoals = keyAPI.prove(proof);
				
			// Check if invInitValid Goal got closed
			if (initGoal.node().isClosed())
				invInitiallyValid = true;
			else
				invInitiallyValid = false;
				
			//restore old proof state
			proof.pruneProof(prevState);
			
			//reset to old invariant - the loopGoal which was previous the openGoal
			//is broken, a new openGoal similar to it was created by pruneProof
			openGoal = proof.openGoals().head();
			setNewLoopInvariantOverwriteOld(openGoal, oldLoopInv);
			
			if (invInitiallyValid)
				initiallyValidCandidates.add(cand);
		}
		return initiallyValidCandidates;
	}

	private static List<Term> parseInvariantStringsAsTerm(List<String> convertedInvariantStrings, DefaultTermParser dtp,
			Services services, NamespaceSet existingNS, AbbrevMap abbr) {
		List<Term> parsedInvariants = new LinkedList<Term>();
    	for (String inv : convertedInvariantStrings) {
    		try {
	        	Term genInvTerm = dtp.parse(new StringReader(inv), null,
				        services, existingNS, abbr);
	        	parsedInvariants.add(genInvTerm);
    		} catch (ParserException e) {
    			e.printStackTrace();
    		}
			
    	}
		return parsedInvariants;
	}

	private static List<String> parseDIGInvariantArray(String rawDIGInvariantArray) {
		if (rawDIGInvariantArray == null || rawDIGInvariantArray.equals(""))
			return new LinkedList<String>();
		
		if (!rawDIGInvariantArray.substring(0, 1).equals("["))
			//DIG Array Format: [p*x + q*y - a == 0, q*r - p*s + 1 == 0, r*x + s*y - b == 0]
			return new LinkedList<String>();
		
		
		String modDIGInvariantArray = rawDIGInvariantArray.replace("[", "").replace("]", "");
		//remove leading spaces (space after each ,)
		String lspacesRegex = "^\\s+";
		List<String> invArrayList = new ArrayList<String>();
		for (String inv : modDIGInvariantArray.split(",")) {
			invArrayList.add(inv.replaceAll(lspacesRegex, ""));
		}

		return invArrayList;
	}
	
	private static List<String> convertDIGInvariantsToJMLFormat(List<String> digInvariants, 
			boolean renameUnderscoreVars, boolean removeWhitespaces) {
		//Input: -u_x^2 + u_x*y + z == 0
		//Output: _x*_x+_x*y+z=0
		//Need to perform 3-4 transformations:
		// ==   -> =
		// -x^3 -> -x*x*x
		//  u_x -> _x
		// optional: remove whitespaces
		
		final String matchBaseExponent = "(\\s*(\\w+?)\\s*\\^\\s*(\\w+))"; //matches -x^3 -> find1: group(1:x^3,2:x,3:3)
		// in order to re-rename underscore vars: u_x -> _x
		//final String matchUnderscoreVars = "\\s*(\\w*(_+?\\w+))\\s*"; 
		final String matchUnderscoreVars = "\\s*u(_\\w+)\\s*"; 
		
		List<String> convertedInvariants = new ArrayList<>();
		for (String inv : digInvariants) {
			if (removeWhitespaces)
				inv = inv.replaceAll(" ", "");
			inv = inv.replaceAll("==", "=");
			
			// Exponent: -x^3 -> -pow(x,3)
			Matcher mExp = Pattern.compile(matchBaseExponent).matcher(inv);
			while (mExp.find()) {
				String baseAndExponent = mExp.group(1);
				String base = mExp.group(2);
				String exponent = mExp.group(3);
				
				String multiplyTerm = base;
				multiplyTerm += IntStream.range(0, Integer.parseInt(exponent) - 1).mapToObj(i -> "*" + base).collect(Collectors.joining(""));
				
				inv = inv.replace(baseAndExponent, multiplyTerm);
			}
			
			// Re-Rename underscore vars: u_x -> _x
			Matcher mUscVar = Pattern.compile(matchUnderscoreVars).matcher(inv);
			while (mUscVar.find()) {
				String prevVar = mUscVar.group(0);
				String newVar = mUscVar.group(1);
				
				inv = inv.replace(prevVar, newVar);
			}
			
			convertedInvariants.add(inv);
		}
		return convertedInvariants;
	}
	
	private static List<String> extractInequalitiesFromTerm(Term userGivenInvariant) {
//	    LESS         { op_name = "lt"; }
//	    |  LESSEQUAL    { op_name = "leq"; }
//	    |  GREATER      { op_name = "gt"; }
//	    |  GREATEREQUAL { op_name = "geq"; }
		List<String> inequalities = new ArrayList<>();
		final String matchInequality = "\\s*(geq|leq|lt|gt)\\s*";
		
	    Pattern pattern = Pattern.compile(matchInequality);
	    String userInvStr = userGivenInvariant.toString();
	    Matcher matcher = pattern.matcher(userInvStr);
	    
	    StringBuilder ineqBuilder = new StringBuilder();
	    // Check all occurrences of ineq
	    while (matcher.find()) {
	        //append ineq keyword like "leq"
	        ineqBuilder.append(matcher.group(1));
	        
	        //append whole content inside leq(..) balanced paranthesis
	        int numOpenParanthesis = 0;
	        int numClosedParanthesis = 0;
	        int i;
	        for (i = matcher.end(); i < userInvStr.length(); i++) {
	        	char c = userInvStr.charAt(i);        
	           	
	        	if (c == '(')
	        		numOpenParanthesis++;
	        	else if (c == ')')
	        		numClosedParanthesis++;
	        	
	        	// First char will be a '('. If we have a matching amount, i is at the index of the matching closing paranthesis leq(..')' <-
	        	if (numOpenParanthesis == numClosedParanthesis) {
	        		break;
	        	}
	        }
	        
	        ineqBuilder.append(userInvStr.substring(matcher.end(), i + 1));
	        
	        //add ineq to list
	        inequalities.add(ineqBuilder.toString());
	        
	        //reset builder
	        ineqBuilder.setLength(0);
	    }
		
		return inequalities;
	}
	
	public static String callDIGGetInvs(final String digPath, final String tracesPath, boolean eqinv, int polDegree) {
		final String eq_or_ineq;
		if (eqinv)
			eq_or_ineq = "eqinv";
		else
			eq_or_ineq = "ineqinv";
		
		String invs = null;
		try {
			//call with polinv or ineqinv -> polinv
			//example call (with pwd=/key/DynamicInvariantsOnDemand): sage -python 'dig/dig/dig.py' eqinv traces.tcs 2
			ProcessBuilder builder = new ProcessBuilder("sage", "-python", digPath, eq_or_ineq, tracesPath, String.valueOf(polDegree), "--debug");
			builder.redirectErrorStream(true);
			Process p;
			p = builder.start();
			
			BufferedWriter toP = new BufferedWriter(new OutputStreamWriter(p.getOutputStream()));
			BufferedReader fromP = new BufferedReader(new InputStreamReader(p.getInputStream()));
			
		    while(!fromP.ready());      
		    
		    String line;
		    String lastLine = null;
		    while((line = fromP.readLine()) != null){
		        System.out.println(line);
		        lastLine = line;
		    }
		    invs = lastLine;
		    System.out.println("Raw Invs: " + invs);
	    
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return invs;
	}
	
	public static Term setNewLoopInvariantOverwriteOld(Goal loopGoal, Term newLoopInv) {
		//create loop spec
		Pair<LoopInvariantBuiltInRuleApp, Services> p = createLoopInvariantBuiltInRuleApp(loopGoal);
		LoopInvariantBuiltInRuleApp ruleApplication = p.first;
		Services services = p.second;
		
		Term oldLoopInv = setNewLoopInvariantOverwriteOld(ruleApplication, services, newLoopInv);
		
		return oldLoopInv;
	}
	
	public static Term setNewLoopInvariantOverwriteOld(
			LoopInvariantBuiltInRuleApp ruleApplication, Services services, Term newLoopInv) {
		
		LoopSpecification spec = ruleApplication.getSpec();
		
		if (spec == null)
			return null;
		
		//retrieve old inv for loop
		Term oldLoopInv = spec.getInvariant(services);
		
		Map<LocationVariable, Term> invariants = new HashMap<>();
		LocationVariable baseHeap  = services.getTypeConverter().getHeapLDT().getHeap();
		invariants.put(baseHeap, newLoopInv);
		
		spec = spec.configurate(invariants, new HashMap<>(), spec.getInternalModifies(), spec.getInternalInfFlowSpec(), null);
		ruleApplication.setLoopInvariant(spec);
		services.getSpecificationRepository().addLoopInvariant(spec);
		
		return oldLoopInv;
	}
	
	public static Pair<LoopInvariantBuiltInRuleApp, Services> createLoopInvariantBuiltInRuleApp(Goal loopGoal) {
		WhileInvariantRule invariantRule = WhileInvariantRule.INSTANCE;
		PosInOccurrence poi = new PosInOccurrence(loopGoal.sequent().succedent().get(1), PosInTerm.getTopLevel(), false);
		Services services = loopGoal.proof().getServices();
		LoopInvariantBuiltInRuleApp ruleApplication = new LoopInvariantBuiltInRuleApp(invariantRule, poi, services);
		ruleApplication = ruleApplication.tryToInstantiate(loopGoal);
		LoopSpecification spec = ruleApplication.getSpec();
		
		return new Pair<LoopInvariantBuiltInRuleApp, Services>(ruleApplication, services);
	}
	
	public static Pair<Term, ImmutableList<Goal>> setNewLoopInvariantOverwriteOldAndApply(Goal loopGoal, Term newLoopInv) {
		//create loop spec
		Pair<LoopInvariantBuiltInRuleApp, Services> p = createLoopInvariantBuiltInRuleApp(loopGoal);
		LoopInvariantBuiltInRuleApp ruleApplication = p.first;
		Services services = p.second;
		
		LoopSpecification spec = ruleApplication.getSpec();
		
		Term oldLoopInv = null;
		//retrieve old inv for loop
		if (spec != null)
			oldLoopInv = spec.getInvariant(services);
		
		Map<LocationVariable, Term> invariants = new HashMap<>();
		LocationVariable baseHeap  = services.getTypeConverter().getHeapLDT().getHeap();
		invariants.put(baseHeap, newLoopInv);
		
		spec = spec.configurate(invariants, new HashMap<>(), spec.getInternalModifies(), spec.getInternalInfFlowSpec(), null);
		ruleApplication.setLoopInvariant(spec);
		services.getSpecificationRepository().addLoopInvariant(spec);
		
		//NOTE: ab hier ist die Invariante schon proofübergreifend gesetzt (im SpecRepo)
		//D.H die folgenden Schritte sind nicht nötig hier
		//Services overlayServices = services.getOverlay(loopGoal.getLocalNamespaces());
		//Needs to be executed (creates initValid, body and usecase branch), else the
		//loopGoal.proof().initConfig.services.specRepo.loopInvs(for this loop) does not get updated
        final ImmutableList<Goal> goalList = loopGoal.apply(ruleApplication);
		
        Pair<Term, ImmutableList<Goal>> ret = new Pair<Term, ImmutableList<Goal>>(oldLoopInv, goalList);
        
		return ret;
	}
	
	//returns Pair<oldInv, GoalList(useCase,Body, InitValid Goals)>
	public static Pair<Term, ImmutableList<Goal>> setNewLoopInvariantOverwriteOldAndApplyToCopy(Goal loopGoal, Term newLoopInv) {
		//We want to update the loopGoal.proof().initConfig.services.specRepo.loopInvs(for this loop)
		Term oldLoopInv;
		
		Proof onlyLoopProof = null;
		try {
			onlyLoopProof = AuxiliaryFunctions.createProof(loopGoal.proof(), "loopProof", loopGoal.sequent());
		} catch (ProofInputException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Goal clonedLoopGoal = onlyLoopProof.openGoals().head();
		
		Pair<LoopInvariantBuiltInRuleApp, Services> p = createLoopInvariantBuiltInRuleApp(clonedLoopGoal);
		LoopInvariantBuiltInRuleApp ruleApplication = p.first;
		Services services = p.second;
		LoopSpecification spec = ruleApplication.getSpec();
		
		Map<LocationVariable, Term> invariants = new HashMap<>();
		TermBuilder termBuilder = services.getTermBuilder();
		Map<LocationVariable, Term> freeInvariants = new HashMap<>();
		Map<LocationVariable, Term> modifies = /*new HashMap<>();//*/spec.getInternalModifies();
		Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs = spec.getInternalInfFlowSpec();
		Term variant = null;
		
		Term update = ruleApplication.posInOccurrence().sequentFormula().formula().sub(0);
		
		LocationVariable baseHeap  = services.getTypeConverter().getHeapLDT().getHeap();
		LocationVariable savedHeap = services.getTypeConverter().getHeapLDT().getSavedHeap();
		invariants.put(baseHeap, newLoopInv);
		
		oldLoopInv = spec.getInvariant(services);
		spec = spec.configurate(invariants, freeInvariants, modifies, infFlowSpecs, variant);
		
		ruleApplication.setLoopInvariant(spec);
        
		services.getSpecificationRepository().addLoopInvariant(spec);
		
		//NOTE: ab hier ist die Invariante schon proofübergreifend gesetzt (im SpecRepo)
		//D.H die folgenden Schritte sind nicht nötig hier
		Services overlayServices = services.getOverlay(clonedLoopGoal.getLocalNamespaces());
		//Needs to be executed (creates initValid, body and usecase branch), else the
		//loopGoal.proof().initConfig.services.specRepo.loopInvs(for this loop) does not get updated
        final ImmutableList<Goal> goalList = ruleApplication.execute(clonedLoopGoal, overlayServices);
		
        Pair<Term, ImmutableList<Goal>> ret = new Pair<Term, ImmutableList<Goal>>(oldLoopInv, goalList);
        
		return ret;
	}
}
