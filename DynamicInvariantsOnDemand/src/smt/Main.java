package smt;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.key_project.util.collection.ImmutableList;

import api.key.KeYAPI;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.Contract;
import dynacode.DynaCode;
import genmethod.MethodGenerator;
import gentest.IGeneratedTest;
import prover.CounterExample;
import prover.InvGenResult;
import prover.Invariant;
import prover.ProofResult;
import prover.ProofWrapper;
import prover.SequentWrapper;

public class Main {

	private static String benchmarksFile1 = "benchmarks/Loop1/Loop1.java";
	private static String benchmarksFile2 = "benchmarks/easyloop1/EasyLoop1.java";
	private static String benchmarksFile3 = "benchmarks/cohen/Cohen.java";
	
//	private static final String digPath = "/home/daniel/git/dig/dig/dig.py";
	private static final String digRelPath = "dig/dig/dig.py";
	//amount of testcases / method calls for the function from which the traces should be obtained
	public static final int maxLoopUnwinds = 12;
	
	private static KeYAPI keyAPI;
	private static Proof clonedProof;
	private static boolean outerLoop;
	
	public static void main(String[] args) {
		outerLoop = true;
		keyAPI = new KeYAPI(benchmarksFile2);
		ProofIndependentSettings.DEFAULT_INSTANCE
        .getTestGenerationSettings().setMaxUnwinds(maxLoopUnwinds);
		ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().intBound = 8;
		
		List<Contract> proofContracts = keyAPI.getContracts();
		ProofResult result = null;
		for(Contract currentContract : proofContracts) {
			Proof currentProof = keyAPI.createProof(currentContract);
			clonedProof = keyAPI.createProof(currentContract);
			result = attemptProve(currentProof);
		}
		if(result != null) System.out.println(result);
	}
	
	private static ProofResult attemptProve(Proof proof) {
		while(!keyAPI.isClosed(proof)) {
			ImmutableList<Goal> openGoals = keyAPI.prove(proof);
			for(Goal currentGoal : openGoals) {
				SequentWrapper currentSequent = keyAPI.getSequent(currentGoal);
				InvGenResult result = attemptInvGen(currentSequent, proof);
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
	
	public static InvGenResult attemptInvGen(SequentWrapper sequent, Proof proof) {
		//FIXME: Daniel - Fix Code for stackedloops, does not work
		if (outerLoop) {
			ProblemFactory.create(clonedProof);
			outerLoop = false;
		} else
			ProblemFactory.create(proof);
		
		List<Term> gamma 		= sequent.getGamma();
		StatementBlock program 	= sequent.getProgram();
		Term phi 				= sequent.getPhi();
		While loop 				= sequent.getLoop();
		Term update				= sequent.getUpdate();
		
		
		System.out.println("start generating modified method with traces code");
		// Generate Program Code with Traces for dynamic execution
		String javaCode = MethodGenerator.generateMethodFromKeYFormat(program, update, loop);
		
		//Write Code to file in workspace
		Path currentPath = Paths.get(System.getProperty("user.dir"));
		Path filePath = Paths.get(currentPath.toString(), "dynacode", "genmethod", "GeneratedMethod.java");
		writeStringToFile(javaCode, filePath.toString());
		
		System.out.println("Start test generation, num cases/calls: " + maxLoopUnwinds);
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
		String invariants = callDIGGetInvs(digAbsPath.toString(), tracesFilePath.toString());
		
		Term suggestedInvariant	= keyAPI.getSuggestedInvariant(loop);
		return new Invariant(suggestedInvariant);
	}
	
	private static IGeneratedTest getGeneratedTest() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (IGeneratedTest) dynacode.newProxyInstance(IGeneratedTest.class,
				"gentest.GeneratedTest");
	}
	public static String formatTracesToDIG(HashMap<String, ArrayList<Integer>> varTraces) {
		StringBuilder sb = new StringBuilder();
		
		//Write Var. line: "x y q a b r"
		int i = 0;
		for (String varName : varTraces.keySet()) {
			if (i != 0)
				sb.append(" ");
			String varNameWithoutUnderscore = varName.replaceFirst("^_", "");
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
		    System.out.println("Invs: " + invs);
	    
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return invs;
	}
}
