package core;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.StringReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import api.key.KeYAPI;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.InfFlowSpec;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import dynacode.DynaCode;
import genmethod.GenMethodData;
import genmethod.MethodGenerator;
import gentest.IGeneratedTest;
import prover.CounterExample;
import prover.InvGenResult;
import prover.Invariant;
import prover.ProofResult;
import prover.ProofWrapper;
import prover.SequentWrapper;
import smt.AuxiliaryFunctions;
import smt.ProblemFactory;

public class Main {
	private static final boolean useGeneratedInvariant = true;
	private static final boolean mockFirstLoopInvariant = false;
	//private static final String mockFirstLoopInvariantString = "-q*_y - r + _x = 0";
	private static final String mockFirstLoopInvariantString = "i - r = 0";
	private static int loopDepthCounter = 0;

	private static final String benchmarksFile1 = "benchmarks/Loop1/Loop1.java";
	private static final String benchmarksFile2 = "benchmarks/easyloop1/EasyLoop1.java";
	private static final String benchmarksFile3 = "benchmarks/cohen/Cohen.java";
	private static final String benchmarksFile4 = "benchmarks/easyloop1nopol/EasyLoop1NoPol.java"; //works
	
	private static final String benchmarksFile5 = "benchmarks/plus/Plus.java";
	private static final String benchmarksFile6 = "benchmarks/square/Square.java";
	private static final String benchmarksFile7 = "benchmarks/times/Times.java";
	private static final String benchmarksFile8 = "benchmarks/timestwo/TimesTwo.java";
	
	private static final String benchmarksFile9 = "benchmarks/squarenozero/SquareNoZero.java";
	
	private static final String benchmarksFile10 = "benchmarks/plusnopol/PlusNoPol.java";
	
	private static final String benchmarksFile11 = "benchmarks/timestwonopol/TimesTwoNoPol.java"; //works
	private static final String benchmarksFile12 = "benchmarks/cohennopol/CohenNoPol.java";
	
	private static final String digRelPath = "dig/dig/dig.py";
	//amount of testcases / method calls for the function from which the traces should be obtained
	public static final int maxLoopUnwinds = 8;
	
	private static KeYAPI keyAPI;
	
	public static void main(String[] args) {
		keyAPI = new KeYAPI(benchmarksFile10);
		
		ProofIndependentSettings.DEFAULT_INSTANCE
        .getTestGenerationSettings().setMaxUnwinds(maxLoopUnwinds);
		//2^(intBound-2) == max possible values of smt (so 2^(6-2))=16 max possible input var value) 
		//int.bound = 8 is max for my system setup
		ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().intBound = 8;
		
		List<Contract> proofContracts = keyAPI.getContracts();
		ProofResult result = null;
		for(Contract currentContract : proofContracts) {
			Proof currentProof = keyAPI.createProof(currentContract);
			result = attemptProve(currentProof);
		}
		if(result != null) System.out.println("Successfully closed proof.");
	}
	
	private static ProofResult attemptProve(Proof proof) {
		while(!keyAPI.isClosed(proof)) {
			ImmutableList<Goal> openGoals = keyAPI.prove(proof);
			for(Goal currentGoal : openGoals) {
				//Iterator it = openGoals.iterator();
				//Goal test = (Goal) it.next();
				//currentGoal = (Goal) it.next();
				SequentWrapper currentSequent = keyAPI.getSequent(currentGoal);
				InvGenResult result = null;
				try {
					result = attemptInvGen(currentSequent, proof);
				} catch (ProofInputException e) {
					e.printStackTrace();
				}
				if(result instanceof CounterExample) {
					CounterExample counterexample = (CounterExample)result;
					return counterexample;
				} else {
					Invariant invariant = (Invariant)result;
					keyAPI.applyInvariantRule(currentGoal, invariant, useGeneratedInvariant);
					attemptProve(proof);
				}
			}
		}
		return new ProofWrapper(proof); 
	}
	
	public static InvGenResult attemptInvGen(SequentWrapper sequent, Proof proof) throws ProofInputException {
		if (!useGeneratedInvariant)
			return null;
		//FIXME: Daniel - Fix Code for stackedloops, does not work
		List<Term> gamma 		= sequent.getGamma();
		StatementBlock program 	= sequent.getProgram();
		Term phi 				= sequent.getPhi();
		While loop 				= sequent.getLoop();
		Term update				= sequent.getUpdate();
		
		if (loop == null) {
			//-> we have no loop here, but we only want to generate loop invariants
			return null;
		}
		loopDepthCounter++;
		
		//clone proof and work on the cloned version, since TestGenerator messes with it
		//we only need to obtain the invariants here, no need to operate on the original proof
		Goal loopGoal = proof.openGoals().head();
		Proof onlyLoopProof = AuxiliaryFunctions.createProof(proof, "loopProof", loopGoal.sequent());
		
		DefaultTermParser dtp = new DefaultTermParser();
		Term conjInvariants = null;
		
		// add update vars to namespace to be able to use the parser for those vars
	    TermBuilder tb = onlyLoopProof.getServices().getTermBuilder();
		Services services = onlyLoopProof.getServices().copy(false);
		//[TEEMP
		ImmutableSet<ProgramVariable> localins = MiscTools.getLocalIns(program, services);
		ImmutableSet<ProgramVariable> localouts = MiscTools.getLocalOuts(program, services);
		//]TEMP
        AbbrevMap abbr = (services.getProof() == null) ? null
                : services.getProof().abbreviations();
        NamespaceSet existingNS = services.getNamespaces();
        UpdateLHSCollectorVisitor updateVisitor = new UpdateLHSCollectorVisitor();
        update.execPreOrder(updateVisitor);
        // somehow the design of KeY leads to this: the local variables declared before loop are not known to this point,
        // only in updates specified. Need to add those to namespace, else the parser throws a "do not know variable" Exc.
        existingNS.programVariables().add(updateVisitor.leftHandVariables);
        
        if (mockFirstLoopInvariant && loopDepthCounter == 1) {
        	System.out.println("Mock First Loop Invariant with Invariant: " + mockFirstLoopInvariantString);
        	try {
	        	conjInvariants = dtp.parse(new StringReader(mockFirstLoopInvariantString), null,
				        services, existingNS, abbr);
    		} catch (ParserException e) {
    			e.printStackTrace();
    		}
        } else {
			System.out.println("Start generating modified method with traces code");
			//FIXME: NOTE: Method Generator knows the user spezified Invariants atm
			// Generate Program Code with Traces for dynamic execution
			String javaCode = MethodGenerator.generateMethodFromKeYFormat(program, update, loop);
			
			System.out.println("inputVars: " + GenMethodData.getInstance().inputVars);
			
			//Write Code to file in workspace
			Path currentPath = Paths.get(System.getProperty("user.dir"));
			Path filePath = Paths.get(currentPath.toString(), "dynacode", "genmethod", "GeneratedMethod.java");
			writeStringToFile(javaCode, filePath.toString());
			
			System.out.println("Start test generation, num cases/calls: " + maxLoopUnwinds);
			Term uselessInv = null;
			try {
				uselessInv = tb.parseTerm("0=0");
			} catch (ParserException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			//delete invariant (the user given Ineq.);
			Term oldLoopInv = setNewLoopInvariantOverwriteOld(loopGoal, uselessInv);
			ProblemFactory.create(onlyLoopProof);
			//restore old inv (user given ineq)
			setNewLoopInvariantOverwriteOld(loopGoal, oldLoopInv);
			
			IGeneratedTest generatedTest = getGeneratedTest();
			
			System.out.println("Call generated test / obtain traces..");
			HashMap<String, ArrayList<Integer>> varTraces = generatedTest.callGeneratedTest();
			
			int numTraces = 0;
			for (ArrayList<Integer> v : varTraces.values()) {
				numTraces = v.size();
			}
			
			System.out.println("Write " + numTraces + " traces in DIG format to file..");
			String tracesDIG = formatTracesToDIG(varTraces);
			//Write Traces to file in workspace
			Path tracesFilePath = Paths.get(currentPath.toString(), "traces.tcs");
			writeStringToFile(tracesDIG, tracesFilePath.toString());
			
			//FIXME: Daniel: better Code
			//Call DIG with traces to get Invariants
			System.out.println("Call DIG with traces file to get Invariants..");
			Path digAbsPath = Paths.get(currentPath.toString(), digRelPath);
			String rawDIGInvariants = callDIGGetPolInvs(digAbsPath.toString(), tracesFilePath.toString());
			
			//TODO: Currently I assume that I get Invariants, but maybe call with more unwinds if no invariant
			List<String> digInvariants = parseDIGInvariantArray(rawDIGInvariants);
			
			
			//---- Convert Invariants to KeY Format ----
			
			List<String> convertedInvariants = convertDIGInvariantsToJMLFormat(digInvariants, true, false);
			System.out.println("JML Invs: " + convertedInvariants);
	        
	        // finally, parse pol. "JML Syntax" Invariants to KeY Format using the KeY Parser
	    	int index = 0;
	    	for (String inv : convertedInvariants) {
	    		try {
		        	Term genInvTerm = dtp.parse(new StringReader(inv), null,
					        services, existingNS, abbr);
					// append to invariant "list"
		        	if (index == 0)
		        		conjInvariants = genInvTerm;
		        	else
		        		conjInvariants = tb.and(conjInvariants, genInvTerm);
		        	
		        	index++;
	    		} catch (ParserException e) {
	    			e.printStackTrace();
	    		}
				
	    	}
        }
        
    	// get user given invariants to extract the inequalities
		Term suggestedInvariant	= keyAPI.getSuggestedInvariant(loop);
		
		// append user given inequalities to DIG obtained polynomial invariant equations
		List<String> inequalities = extractInequalitiesFromTerm(suggestedInvariant);
		for (String ineq : inequalities) {
			try {
				Term ineqTerm = dtp.parse(new StringReader(ineq), null,
				        services, existingNS, abbr);
				conjInvariants = tb.and(conjInvariants, ineqTerm);
			} catch (ParserException e) {
				e.printStackTrace();
			}
		}
		System.out.println("Full Inv-Term with User given Ineq: " + conjInvariants.toString());
		
		boolean invInitiallyValid = isInvInitiallyValid(conjInvariants, loopGoal);
		System.out.println("invInitiallyValid: " + invInitiallyValid);
		
		return new Invariant(conjInvariants);
	}
	
	private static List<String> parseDIGInvariantArray(String rawDIGInvariantArray) {
		if (rawDIGInvariantArray == null || rawDIGInvariantArray.equals(""))
			return null;
		
		if (!rawDIGInvariantArray.substring(0, 1).equals("["))
			//DIG Array Format: [p*x + q*y - a == 0, q*r - p*s + 1 == 0, r*x + s*y - b == 0]
			return null;
		
		
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
		//Output: pow(_x,2)+_x*y+z=0
		//Need to perform 2-4 transformations:
		// ==   -> =
		// -x^3 -> -pow(x,3)
		// optional: u_x -> _x
		// optional: remove whitespaces
		
		final String matchBaseExponent = "(\\s*(\\w+?)\\s*\\^\\s*(\\w+))"; //matches -x^3 -> find1: group(1:x^3,2:x,3:3)
		// in order to re-rename underscore vars: u_x -> _x
		final String matchUnderscoreVars = "\\s*(\\w*(_+?\\w+))\\s*"; 
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
				
				//FIXME: replace (all) is ugly here but should work
				inv = inv.replace(baseAndExponent, multiplyTerm);
			}
			
			// Re-Rename underscore vars: u_x -> _x
			Matcher mUscVar = Pattern.compile(matchUnderscoreVars).matcher(inv);
			while (mUscVar.find()) {
				String prevVar = mUscVar.group(1);
				String newVar = mUscVar.group(2);
				
				//FIXME: replace (all) is ugly here but should work
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
	
	private static IGeneratedTest getGeneratedTest() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (IGeneratedTest) dynacode.newProxyInstance(IGeneratedTest.class,
				"gentest.GeneratedTest");
	}
	
	public static String formatTracesToDIG(HashMap<String, ArrayList<Integer>> varTraces) {
		StringBuilder sb = new StringBuilder();
		
		//FIXME: sage works with first sign alphanumeric variables, thus conversion: _x -> u_x
		//Write Var. line: "u_x y q a b r"
		int i = 0;
		for (String varName : varTraces.keySet()) {
			if (i != 0)
				sb.append(" ");
			String varNameWithoutUnderscore = varName.replaceFirst("^_", "u_");
			sb.append(varNameWithoutUnderscore);
			i++;
		}
		sb.append(System.lineSeparator());
		
		ArrayList<ArrayList<Integer>> values = new ArrayList<ArrayList<Integer>>();
		for (Map.Entry<String, ArrayList<Integer>> e : varTraces.entrySet()) {
			values.add(e.getValue());
		}
		
		for (int j = 0; j < values.get(0).size(); j++) {
			for (int k = 0; k < values.size(); k++) {
				sb.append(values.get(k).get(j));
				sb.append(" ");
			}
			sb.append(System.lineSeparator());
		}
		
		return sb.toString();
	}
	
	public static void writeStringToFile(String content, String fileDest) {
	    try {
	    	BufferedWriter writer = new BufferedWriter(new FileWriter(fileDest));
			writer.write(content);
			writer.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static String callDIGGetPolInvs(final String digPath, final String tracesPath) {
		String invs = null;
		try {
			//call with polinv or ineqinv -> polinv
			ProcessBuilder builder = new ProcessBuilder("sage", "-python", digPath, "polinv",tracesPath);
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
		WhileInvariantRule invariantRule = WhileInvariantRule.INSTANCE;
		PosInOccurrence poi = new PosInOccurrence(loopGoal.sequent().succedent().get(1), PosInTerm.getTopLevel(), false);
		Services services = loopGoal.proof().getServices();
		LoopInvariantBuiltInRuleApp ruleApplication = new LoopInvariantBuiltInRuleApp(invariantRule, poi, services);
		ruleApplication = ruleApplication.tryToInstantiate(loopGoal);
		LoopSpecification spec = ruleApplication.getSpec();
		
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
		
		WhileInvariantRule invariantRule = WhileInvariantRule.INSTANCE;
		PosInOccurrence poi = new PosInOccurrence(clonedLoopGoal.sequent().succedent().get(1), PosInTerm.getTopLevel(), false);
//		TermServices services = keyAPI.myEnvironment.getServices();
//		LoopInvariantBuiltInRuleApp ruleApplication = new LoopInvariantBuiltInRuleApp(invariantRule, poi, services);
//		ruleApplication = ruleApplication.tryToInstantiate(clonedLoopGoal);
//		LoopSpecification spec = ruleApplication.getSpec();
//		Services serv = clonedLoopGoal.proof().getServices();
		Services services = clonedLoopGoal.proof().getServices();
		LoopInvariantBuiltInRuleApp ruleApplication = new LoopInvariantBuiltInRuleApp(invariantRule, poi, services);
		ruleApplication = ruleApplication.tryToInstantiate(clonedLoopGoal);
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
		
//		//apply updates WhileInvariantRule:
//        final Term focusTerm = ruleApplication.posInOccurrence().subTerm();
//        Pair<Term, Term> updates = null;
//        if (focusTerm.op() instanceof UpdateApplication) {
//        	updates = new Pair<Term, Term>(UpdateApplication.getUpdate(focusTerm),
//                    UpdateApplication.getTarget(focusTerm));
//        } else {
//        	updates = new Pair<Term, Term>(services.getTermBuilder().skip(), focusTerm);
//        }
//
//    	final Term u        = updates.first;
//    	final Term progPost = updates.second;
//
//    	//focus (below update) must be modality term
//            if (!(progPost.op() instanceof Modality)) {
//                try {
//					throw new Exception();
//				} catch (Exception e) {
//					// TODO Auto-generated catch block
//					e.printStackTrace();
//				}
//            }
//
//    	//active statement must be while loop
//    	final While loop = ruleApplication.getLoopStatement();
//
//    	if (spec == null)
//			try {
//				throw new RuleAbortException("no invariant found");
//			} catch (RuleAbortException e) {
//				// TODO Auto-generated catch block
//				e.printStackTrace();
//			}
//
//    	//collect self, execution context
//    	final MethodFrame innermostMethodFrame =
//    	        JavaTools.getInnermostMethodFrame(progPost.javaBlock(), services);
//    	if (innermostMethodFrame != null) {
//    	    spec = spec.setTarget(innermostMethodFrame.getProgramMethod());
//    	}
//
//    	final Term selfTerm = innermostMethodFrame == null
//    	                      ? null
//    	                      : MiscTools.getSelfTerm(innermostMethodFrame, services);
//
//    	final ExecutionContext innermostExecutionContext =
//    	        innermostMethodFrame == null
//    	        ? null
//    	        : (ExecutionContext) innermostMethodFrame.getExecutionContext();
//    	services.getSpecificationRepository().addLoopInvariant(spec);
        
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
	
	public static boolean isInvInitiallyValid(Term inv, Goal loopGoal) {
		//TODO: testGeneration "destroyed" the proof
		//FIXME: WICHTIG: Obwohl hier auf der copy gearbeitet wird, werden die richtigen Invarianten ersetzt
		Pair<Term, ImmutableList<Goal>> oldInvAndGoalList = setNewLoopInvariantOverwriteOldAndApplyToCopy(loopGoal, inv);
		Term oldLoopInv = oldInvAndGoalList.first;
		final ImmutableList<Goal> goalList = oldInvAndGoalList.second;
		//}
		// { From WhileInvariantRule.apply
        Goal initGoal = goalList.tail().tail().head();
        Goal bodyGoal = goalList.tail().head();
        Goal useGoal = goalList.head();
        //}
		
        Sequent invInitValidSequent = initGoal.sequent();
		boolean invInitiallyValid = false;
		try {
			Proof invInitValidProof = AuxiliaryFunctions.createProof(loopGoal.proof(), "invInitValidProof", invInitValidSequent);
			
			ImmutableList<Goal> openGoals = keyAPI.prove(invInitValidProof);
			
			// Check if invInitValid Goal got closed
			if (openGoals.isEmpty())
				invInitiallyValid = true;
			else
				invInitiallyValid = false;
			
		} catch (ProofInputException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		Sequent invBodySequent = bodyGoal.sequent();
		boolean invBody = false;
		try {
			Proof invBodyProof = AuxiliaryFunctions.createProof(loopGoal.proof(), "invBodyProof", invBodySequent);
			
			ImmutableList<Goal> openGoals = keyAPI.prove(invBodyProof);
			
			// Check if invInitValid Goal got closed
			if (openGoals.isEmpty())
				invBody = true;
			else
				invBody = false;
			
		} catch (ProofInputException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		Sequent invUseCaseSequent = useGoal.sequent();
		boolean invUseCase = false;
		try {
			Proof invUseCaseProof = AuxiliaryFunctions.createProof(loopGoal.proof(), "invUseCaseProof", invUseCaseSequent);
			
			ImmutableList<Goal> openGoals = keyAPI.prove(invUseCaseProof);
			
			// Check if invInitValid Goal got closed
			if (openGoals.isEmpty())
				invUseCase = true;
			else
				invUseCase = false;
			
		} catch (ProofInputException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		//reset to old invariant
		setNewLoopInvariantOverwriteOld(loopGoal, oldLoopInv);
		
		return invInitiallyValid;
	}

}
