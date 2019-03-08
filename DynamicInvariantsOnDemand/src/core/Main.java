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

import api.key.KeYAPI;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.InfFlowSpec;
import dynacode.DynaCode;
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
	private static final boolean mockFirstLoopInvariant = false;
	private static final String mockFirstLoopInvariantString = "-q*_y - r + _x = 0";
	private static int loopDepthCounter = 0;

	private static final String benchmarksFile1 = "benchmarks/Loop1/Loop1.java";
	private static final String benchmarksFile2 = "benchmarks/easyloop1/EasyLoop1.java";
	private static final String benchmarksFile3 = "benchmarks/cohen/Cohen.java";
	private static final String benchmarksFile4 = "benchmarks/easyloop1/EasyLoop1NoPol.java";
	
	private static final String digRelPath = "dig/dig/dig.py";
	//amount of testcases / method calls for the function from which the traces should be obtained
	public static final int maxLoopUnwinds = 5;
	
	private static KeYAPI keyAPI;
	
	public static void main(String[] args) {
		keyAPI = new KeYAPI(benchmarksFile3);
		ProofIndependentSettings.DEFAULT_INSTANCE
        .getTestGenerationSettings().setMaxUnwinds(maxLoopUnwinds);
		ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().intBound = 8;
		//ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().intBound = 20;
		
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
					keyAPI.applyInvariantRule(currentGoal, invariant);
					attemptProve(proof);
				}
			}
		}
		return new ProofWrapper(proof); 
	}
	
	public static InvGenResult attemptInvGen(SequentWrapper sequent, Proof proof) throws ProofInputException {
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
		//TODO: .head()? more possibilities?
		Goal loopGoal = proof.openGoals().head();
		Proof onlyLoopProof = AuxiliaryFunctions.createProof(proof, "loopProof", loopGoal.sequent());
		
		DefaultTermParser dtp = new DefaultTermParser();
		Term conjInvariants = null;
		
		// add update vars to namespace to be able to use the parser for those vars
	    TermBuilder tb = onlyLoopProof.getServices().getTermBuilder();
		Services services = onlyLoopProof.getServices().copy(false);
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
			// Generate Program Code with Traces for dynamic execution
			String javaCode = MethodGenerator.generateMethodFromKeYFormat(program, update, loop);
			
			//Write Code to file in workspace
			Path currentPath = Paths.get(System.getProperty("user.dir"));
			Path filePath = Paths.get(currentPath.toString(), "dynacode", "genmethod", "GeneratedMethod.java");
			writeStringToFile(javaCode, filePath.toString());
			
			System.out.println("Start test generation, num cases/calls: " + maxLoopUnwinds);
			ProblemFactory.create(onlyLoopProof);
			
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
			String rawDIGInvariants = callDIGGetInvs(digAbsPath.toString(), tracesFilePath.toString());
			
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
		
		boolean invInitiallyValid = isInvInitiallyValid(conjInvariants, proof.openGoals().head());
		System.out.println("invInitiallyValid: " + invInitiallyValid);
		
		return new Invariant(conjInvariants);
	}
	
	private static List<String> parseDIGInvariantArray(String rawDIGInvariantArray) {
		if (rawDIGInvariantArray == null || rawDIGInvariantArray.equals(""))
			return null;
		
		if (!rawDIGInvariantArray.substring(0, 1).equals("["))
			//DIG Array Format: [p*x + q*y - a == 0, q*r - p*s + 1 == 0, r*x + s*y - b == 0]
			return null;
		
		String[] invArray;
		String modDIGInvariantArray = rawDIGInvariantArray.replace("[", "").replace("]", "");
		invArray = modDIGInvariantArray.split("^,");
		
		return new ArrayList<String>(Arrays.asList(invArray));
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
		//TODO: Bug: and(leq(Z(0(#)),r),equals(_x,javaAddInt(javaMulInt(q,_y),r)))<<SC>>
		//-> non greedy matching: stops at Z closing paranthesis. No Problem, if Z is the second operator of leq
		// greedy matching does not work. We will stop at the last parantheses of the whole expression
		// maybe regex recursion to find () groups and then analyze manually in java
		final String matchInequality = "\\s*((?:geq|leq|lt|gt)\\(.*?\\))\\s*";
		List<String> inequalities = new ArrayList<>();
		Matcher mIneq = Pattern.compile(matchInequality).matcher(userGivenInvariant.toString());
		while (mIneq.find()) {
			String inequality = mIneq.group(1);
			
			// To this point, since the matcher is not greedy, only the first closing parenthesis ")" will be matched
			// -> append ")" as many as open ones
			
			int countOpeningParenthesis = inequality.length() - inequality.replace("(", "").length();
			final int countClosingParenthesis = 1;
			
			assert countOpeningParenthesis >= countClosingParenthesis;
			int diff = countOpeningParenthesis - countClosingParenthesis;
			
			String closingParDiffTimes = IntStream.range(0, diff).mapToObj(i -> ")").collect(Collectors.joining(""));
			inequality += closingParDiffTimes;
			
			inequalities.add(inequality);
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
	
	public static String callDIGGetInvs(final String digPath, final String tracesPath) {
		String invs = null;
		try {
			ProcessBuilder builder = new ProcessBuilder("sage", "-python", digPath, tracesPath);
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
	
	public static boolean isInvInitiallyValid(Term inv, Goal loopGoal) {
		//TODO: testGeneration "destroyed" the proof
		Proof proof = loopGoal.proof();
		boolean invInitiallyValid = false;
		try {
			Proof onlyLoopProof = AuxiliaryFunctions.createProof(proof, "loopProof", loopGoal.sequent());
			Goal clonedLoopGoal = onlyLoopProof.openGoals().head();
		
			//invInitValidSequent generieren
			//{ Copy from KeYAPI
			WhileInvariantRule invariantRule = WhileInvariantRule.INSTANCE;
			PosInOccurrence poi = new PosInOccurrence(clonedLoopGoal.sequent().succedent().get(1), PosInTerm.getTopLevel(), false);
			TermServices services = keyAPI.myEnvironment.getServices();
			LoopInvariantBuiltInRuleApp ruleApplication = new LoopInvariantBuiltInRuleApp(invariantRule, poi, services);
			ruleApplication = ruleApplication.tryToInstantiate(clonedLoopGoal);
			LoopSpecification spec = ruleApplication.getSpec();
			Services serv = clonedLoopGoal.proof().getServices();
			
			Map<LocationVariable, Term> invariants = new HashMap<>();
			TermBuilder termBuilder = services.getTermBuilder();
			Map<LocationVariable, Term> freeInvariants = new HashMap<>();
			Map<LocationVariable, Term> modifies = /*new HashMap<>();//*/spec.getInternalModifies();
			Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs = spec.getInternalInfFlowSpec();
			Term variant = null;
			
			Term update = ruleApplication.posInOccurrence().sequentFormula().formula().sub(0);
			
			LocationVariable baseHeap  = serv.getTypeConverter().getHeapLDT().getHeap();
			LocationVariable savedHeap = serv.getTypeConverter().getHeapLDT().getSavedHeap();
			invariants.put(baseHeap, inv);
			spec = spec.configurate(invariants, freeInvariants, modifies, infFlowSpecs, variant);
			
			ruleApplication.setLoopInvariant(spec);
			
			//} KeYAPI
			
			// { Copy From Goal.apply
	        Services overlayServices = onlyLoopProof.getServices().getOverlay(clonedLoopGoal.getLocalNamespaces());
	        final ImmutableList<Goal> goalList = ruleApplication.execute(clonedLoopGoal, overlayServices);
			//}
			// { From WhileInvariantRule.apply
	        Goal initGoal = goalList.tail().tail().head();
	        Goal bodyGoal = goalList.tail().head();
	        Goal useGoal = goalList.head();
	        //}
			
	        Sequent invInitValidSequent = initGoal.sequent();
			try {
				Proof invInitValidProof = AuxiliaryFunctions.createProof(onlyLoopProof, "invInitValidProof", invInitValidSequent);
				
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
				Proof invBodyProof = AuxiliaryFunctions.createProof(onlyLoopProof, "invBodyProof", invBodySequent);
				
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
				Proof invUseCaseProof = AuxiliaryFunctions.createProof(onlyLoopProof, "invUseCaseProof", invUseCaseSequent);
				
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
		} catch (ProofInputException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		return invInitiallyValid;
	}
}
