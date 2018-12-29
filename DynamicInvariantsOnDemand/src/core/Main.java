package core;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map.Entry;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import api.key.KeYAPI;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.Contract;
import prover.CounterExample;
import prover.InvGenResult;
import prover.Invariant;
import prover.ProofResult;
import prover.ProofWrapper;
import prover.SequentWrapper;

public class Main {

	private static String benchmarksFile1 = "benchmarks/Cohen.java";
	private static String benchmarksFile2 = "benchmarks/Loop1.java";
	private static KeYAPI keyAPI;
	
	private static boolean firstCallInvGen = true;
	
	public static void main(String[] args) {
		keyAPI = new KeYAPI(benchmarksFile1);
		List<Contract> proofContracts = keyAPI.getContracts(); // Kopf von Cohen, public normal_behavior @ requires (0 <= x) && (0 < y); @ ensures \result*y <= x && x <= (\result+1)*y;
		ProofResult result;
		for(Contract currentContract : proofContracts) {
			Proof currentProof = keyAPI.createProof(currentContract); // Contract nochmal umgeschrieben (in Taclet?)
			result = attemptProve(currentProof);
			System.out.println("hi");
		}
		System.out.println("done");
	}
	
	private static ProofResult attemptProve(Proof proof) {
		while(!keyAPI.isClosed(proof)) {
			ImmutableList<Goal> openGoals = keyAPI.prove(proof); // Annahme: Auto-Proof bis 1. Open Goal. erstes Goal ist komplettes Cohen Programm (da direkt Loop kommt)
			for(Goal currentGoal : openGoals) {
				SequentWrapper currentSequent = keyAPI.getSequent(currentGoal);
				// FIXME: better solution here. Also, this won't work for multiple functions in one class
				InvGenResult result = attemptInvGen(currentSequent, firstCallInvGen);
				if (firstCallInvGen) firstCallInvGen = false;
				if(result instanceof CounterExample) {
					CounterExample counterexample = (CounterExample)result;
					return counterexample;
				} else {
					Invariant invariant = (Invariant)result;
					keyAPI.applyInvariantRule(currentGoal, invariant);
					attemptProve(proof); //!!! Rekursiv. Beim ersten Durchlauf bis hier: Invariant für Loop 1 angewendet. Dadurch beim nächsten attemptProve, openGoal mit "abgerollter"/gelöster 1. Schleife
				}
			}
		}
		return new ProofWrapper(proof); 
	}
	
	public static InvGenResult attemptInvGen(SequentWrapper sequent, boolean firstCall) {
		List<Term> gamma 		= sequent.getGamma();   // [wellFormed(heap), equals(boolean::select(heap,self,java.lang.Object::<created>),TRUE), equals(SimpleExamples::exactInstance(self),TRUE), measuredByEmpty, geq(x,Z(0(#))), geq(y,Z(1(#))), not(equals(self,null))]
		StatementBlock program 	= sequent.getProgram(); // {while ( _y<=r ) {     int a = 1;     int b = _y;                         while ( 2*b<=r ) {       a=2*a;       b=2*b;     }     r=r-b;     q=q+a;   }                 return  q; }
		Term phi 				= sequent.getPhi();		// Cohen Kopf: and(and(and(leq(mul(y,result),x),geq(mul(y,result),add(x,mul(y,Z(neglit(1(#)))))))<<SC>>,java.lang.Object::<inv>(heap,self)<<impl>>)<<SC>>,equals(exc,null)<<impl>>)
		While loop 				= sequent.getLoop();	// while ( _y<=r ) {   int a = 1;   int b = _y;                         while ( 2*b<=r ) {     a=2*a;     b=2*b;   }   r=r-b;   q=q+a; }
		Term update				= sequent.getUpdate();  // parallel-upd(parallel-upd(parallel-upd(parallel-upd(elem-update(_x)(x),elem-update(_y)(y)),elem-update(exc)(null)),elem-update(q)(Z(0(#)))),elem-update(r)(x))
														// Für innere Invariante: parallel-upd(parallel-upd(parallel-upd(parallel-upd(parallel-upd(parallel-upd(elem-update(_x)(x),elem-update(_y)(y)),elem-update(exc)(null)),parallel-upd(elem-update(heapBefore_LOOP)(heap),parallel-upd(parallel-upd(elem-update(q)(q_0),elem-update(r)(r_0)),elem-update(heap)(anon(heap,empty,anon_heap_LOOP<<anonHeapFunction>>))))),elem-update(exc_1)(FALSE)),elem-update(a)(Z(1(#)))),elem-update(b_2)(y))
														// Also a = 1, b_2 = y, neue Temp Vars für q und r (q_0, r_0). Warum a, aber b_2?
		if (firstCall) {	
			// Hier möchte ich jetzt eine Invariante generieren
			// Dazu 1. Java Code erstellen, der ausführbar ist, um traces zu erhalten
			// Java Code als File abspeichern (warum? warum nicht einfach in memory)
			// FIXME innere Schleife behandeln (nicht nur first call)
			String javaCode = generateMethodFromKeYFormat(program, update);
			
			//Write Code to file in workspace
			Path currentPath = Paths.get(System.getProperty("user.dir"));
			Path filePath = Paths.get(currentPath.toString(), "dynacode", "sample", "GeneratedMethod.java");
			writeStringToFile(javaCode, filePath.toString());
		}
	    
		Term suggestedInvariant	= keyAPI.getSuggestedInvariant(loop); // Erste (User angegebene) Loop Invariante: and(leq(Z(0(#)),r),equals(_x,javaAddInt(javaMulInt(q,_y),r)))<<SC>>
		return new Invariant(suggestedInvariant);
	}
	
	public static String generateMethodFromKeYFormat(StatementBlock program, Term update) {
		//FIXME: sind in Update wirklich immer alle relevanten Variablen? Siehe ImmutableList<Goal> openGoals = keyAPI.prove(proof);
		//FIXME: was passiert, wenn darüber schon autoprooft wird, und die Variablen quasi schon älter sind, wurden dann die Updates schon vorher durchgeführt und die Variablen tauchen hier nicht mehr auf?
		// Extrahiere Funktions-Input-Variablen (die die Zuweisung wie elem-update(_x)(x) haben) und extrahiere weitere Variablen, die relevant in der Schleife sind (elem-update(q)(Z(0(#))) & elem-update(r)(x))
		TermVariableNameCollectorVisitor varNameCollector = new TermVariableNameCollectorVisitor();
		update.execPreOrder(varNameCollector);
		
		StringBuilder javaCodeBuilder = new StringBuilder();
		StringBuilder functionHeaderParameterBuilder = new StringBuilder();
		StringBuilder localVariableAssignmentBuilder = new StringBuilder();
		StringBuilder functionHeaderBuilder = new StringBuilder();
		
		final String classHeader = "public class foo {";
		
		// FIXME: Better Logic
		String functionType = "";
		if (program.toString().contains("return;") || !program.toString().contains("return"))
			functionType = "void";
		else
			functionType = "int";
		functionHeaderBuilder.append("public ");
		functionHeaderBuilder.append(functionType);
		functionHeaderBuilder.append(" bar(");
		
		
		// Extrahiere input / parameter Variables von visitor
		// Und local Variables mit Assignment um deren Anfangs-Zuweisungen zum Programm zu ergänzen (fehlt in StatementBlock)
		ArrayList<String> inputVars = new ArrayList<String>();
		HashMap<String, String> localVarsAndAssignment = new HashMap<String, String>();
		for (Entry<String, String> e : varNameCollector.variables.entrySet()) {
			// Function parameter Variables start with underscore _
			String variableName = e.getKey().toString();
			if (variableName.startsWith("_")) {
				inputVars.add(variableName);
			} 
			else {
				localVarsAndAssignment.put(e.getKey(), e.getValue());
			}
		}
		
		// Build local variable assignments
		for (Entry<String, String> e : localVarsAndAssignment.entrySet()) {
			localVariableAssignmentBuilder.append(e.getKey());
			localVariableAssignmentBuilder.append(" = ");
			localVariableAssignmentBuilder.append(e.getValue());
			localVariableAssignmentBuilder.append(";");
		}
		
		// Build Parameter List for Function
		for (String var : inputVars) {
			//only integer supported atm
			if (functionHeaderParameterBuilder.length() > 0) 
				functionHeaderParameterBuilder.append(", ");
			functionHeaderParameterBuilder.append("int ");
			functionHeaderParameterBuilder.append(var);
		}
		functionHeaderBuilder.append(functionHeaderParameterBuilder.toString());
		functionHeaderBuilder.append(")");
		
		// Build Code
		javaCodeBuilder.append(classHeader);
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append(functionHeaderBuilder.toString());
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append("{");
		javaCodeBuilder.append(localVariableAssignmentBuilder.toString());
		javaCodeBuilder.append(System.lineSeparator());
		//Remove leading "{" of StatementBlock to inject variable assignments
		javaCodeBuilder.append(program.toSource().replaceAll("^\\{+", ""));
		// Close Class declaration
		javaCodeBuilder.append(System.lineSeparator());
		javaCodeBuilder.append("}");

		return javaCodeBuilder.toString();
	}

	public static ArrayList<String> getArrayListVarStringsFromVars(ArrayList<String> variables, boolean beginLoop) {
		// beginLoop=false -> Names with afterLoop.
		// Example: Returns for variables(x,y): ArrayList<Integer> beginLoop_x = new ArrayList<Integer>();
		//										ArrayList<Integer> beginLoop_y = new ArrayList<Integer>();
		ArrayList<String> arrayListVarStrings = new ArrayList<String>();
		
		final String BEGIN_DECLARATION = "ArrayList<Integer> ";
		final String PREFIX_VAR_NAME = beginLoop ? "beginLoop" : "afterLoop";
		final String END_DECLARATION = " = new ArrayList<Integer>();";
		
		StringBuilder arrayListVarStringBuilder = new StringBuilder();
		for (String var : variables) {
			arrayListVarStringBuilder.append(BEGIN_DECLARATION);
			arrayListVarStringBuilder.append(PREFIX_VAR_NAME);
			arrayListVarStringBuilder.append("_");
			arrayListVarStringBuilder.append(var);
			arrayListVarStringBuilder.append(END_DECLARATION);
			
			//Add ArrayListVarStrings for this variable to the returned List
			arrayListVarStrings.add(arrayListVarStringBuilder.toString());
			//Clear Builder for next var
			arrayListVarStringBuilder.setLength(0);
		}
		
		return arrayListVarStrings;
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

	
}