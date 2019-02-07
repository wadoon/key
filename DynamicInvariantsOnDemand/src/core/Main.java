package core;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import api.key.KeYAPI;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SemanticsBlastingMacro;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SMTSettings;
import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.Debug;
import genmethod.MethodGenerator;
import prover.CounterExample;
import prover.InvGenResult;
import prover.Invariant;
import prover.ProofResult;
import prover.ProofWrapper;
import prover.SequentWrapper;

public class Main {

	private static String benchmarksFile1 = "benchmarks/cohen/Cohen.java";
	private static String benchmarksFile2 = "benchmarks/easyloop1/EasyLoop1.java";
	private static KeYAPI keyAPI;
	
	private static boolean firstCallInvGen = true;
	
	public static void main(String[] args) {
		keyAPI = new KeYAPI(benchmarksFile2);
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
				InvGenResult result = attemptInvGen(currentSequent, firstCallInvGen, proof, currentGoal);
				if (firstCallInvGen) firstCallInvGen = false;
				if(result instanceof CounterExample) {
					CounterExample counterexample = (CounterExample)result;
					return counterexample;
				} else {
					Invariant invariant = (Invariant)result;
					keyAPI.applyInvariantRule(currentGoal, invariant);
					attemptProve(proof); //!!! Rekursiv. Beim ersten Durchlauf bis hier: Invariant f�r Loop 1 angewendet. Dadurch beim n�chsten attemptProve, openGoal mit "abgerollter"/gel�ster 1. Schleife
				}
			}
		}
		return new ProofWrapper(proof); 
	}
	
	public static InvGenResult attemptInvGen(SequentWrapper sequent, boolean firstCall, Proof proof, Goal currentGoal) {
		List<Term> gamma 		= sequent.getGamma();   // [wellFormed(heap), equals(boolean::select(heap,self,java.lang.Object::<created>),TRUE), equals(SimpleExamples::exactInstance(self),TRUE), measuredByEmpty, geq(x,Z(0(#))), geq(y,Z(1(#))), not(equals(self,null))]
		StatementBlock program 	= sequent.getProgram(); // {while ( _y<=r ) {     int a = 1;     int b = _y;                         while ( 2*b<=r ) {       a=2*a;       b=2*b;     }     r=r-b;     q=q+a;   }                 return  q; }
		Term phi 				= sequent.getPhi();		// Cohen Kopf: and(and(and(leq(mul(y,result),x),geq(mul(y,result),add(x,mul(y,Z(neglit(1(#)))))))<<SC>>,java.lang.Object::<inv>(heap,self)<<impl>>)<<SC>>,equals(exc,null)<<impl>>)
		While loop 				= sequent.getLoop();	// while ( _y<=r ) {   int a = 1;   int b = _y;                         while ( 2*b<=r ) {     a=2*a;     b=2*b;   }   r=r-b;   q=q+a; }
		Term update				= sequent.getUpdate();  // parallel-upd(parallel-upd(parallel-upd(parallel-upd(elem-update(_x)(x),elem-update(_y)(y)),elem-update(exc)(null)),elem-update(q)(Z(0(#)))),elem-update(r)(x))
														// F�r innere Invariante: parallel-upd(parallel-upd(parallel-upd(parallel-upd(parallel-upd(parallel-upd(elem-update(_x)(x),elem-update(_y)(y)),elem-update(exc)(null)),parallel-upd(elem-update(heapBefore_LOOP)(heap),parallel-upd(parallel-upd(elem-update(q)(q_0),elem-update(r)(r_0)),elem-update(heap)(anon(heap,empty,anon_heap_LOOP<<anonHeapFunction>>))))),elem-update(exc_1)(FALSE)),elem-update(a)(Z(1(#)))),elem-update(b_2)(y))
														// Also a = 1, b_2 = y, neue Temp Vars f�r q und r (q_0, r_0). Warum a, aber b_2?
		if (firstCall) {
			/* Z3 BELEGUNGEN TEST
			*/
			
		    final Collection<SMTProblem> problems = new LinkedList<SMTProblem>();
		    TermBuilder tb = proof.getServices().getTermBuilder();
//		    final String testRandomXTerm = "geq(Z(5(#)),Z(0(#)))"; _> valid
		    Term gammaTerm = gamma.get(4);
		    Term customTerm = null;
			final String originalDIGInv = "-x^2 + x*y + z == 0";
			String modDIGInv = "-pow(x,2) + x*y + z == 0";
		    try {
				Term inv = tb.parseTerm(originalDIGInv);
			} catch (ParserException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
		    
		    try {
		    	customTerm = tb.not(tb.parseTerm("geq(x,Z(5(#)))"));
			} catch (ParserException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		    TermVariableVisitor termVariableVisitor = new TermVariableVisitor();
		    gammaTerm.execPreOrder(termVariableVisitor);
		    
		    LocationVariable gammaVarX = (LocationVariable) gammaTerm.subs().get(0).op();
			Term varXTerm = tb.var(gammaVarX);
			Term lastCounterExample = tb.zTerm(0);
		    Term excludeLastCounterExample = tb.not(tb.equals(varXTerm, lastCounterExample));
		    Term negatedGammaTerm = tb.not(gammaTerm);
		    Term negatedGammaExcludedTerm = tb.and(negatedGammaTerm, excludeLastCounterExample);
		    
		    //gammaTermClone.sub(0)
		    
		    ArrayList<String> varStrings = new ArrayList();
		    termVariableVisitor.variables.forEach(v -> varStrings.add(v.toString()));
		    String gammaTermString = gammaTerm.toString();
		    //TODO: wie variablen im Term sinnvoll ersetzen?
		    
//		    Term randomXTerm = null;
//		    Term varXTerm = null;
//		    Term varXEqualsNumberTerm = null;
//		    Term andTerm = null;
//		    LocationVariable gammaVarX = (LocationVariable) gammaTerm.subs().get(0).op();
//			randomXTerm = tb.zTerm(1);
////				varXTerm = tb.parseTerm("x");
//			varXTerm = tb.var(gammaVarX);
//			Term t = null;
////			try {
////				t = tb.parseTerm(testRandomXTerm);
////			} catch (ParserException e) {
////				// TODO Auto-generated catch block
////				e.printStackTrace();
////			}
//			varXEqualsNumberTerm = tb.equals(varXTerm, randomXTerm);
//			andTerm = tb.and(gammaTerm, varXEqualsNumberTerm);
//		    problems.add(new SMTProblem(gamma.get(4)));
			SMTProblem smtproblem = new SMTProblem(currentGoal);
//			smtproblem.setTerm(negatedGammaExcludedTerm);
			smtproblem.setTerm(customTerm);
		    problems.add(smtproblem);
		    
		    //create special smt settings for test case generation
		    final ProofIndependentSMTSettings piSettings = ProofIndependentSettings.DEFAULT_INSTANCE
		          .getSMTSettings().clone();
		    piSettings.setMaxConcurrentProcesses(1);
		    piSettings.timeout = 500000000;
		    final ProofDependentSMTSettings pdSettings = proof.getSettings()
		          .getSMTSettings().clone();
		    //pdSettings.invariantForall = settings.invaraiantForAll();
		    // invoke z3 for counterexamples
		    final SMTSettings smtsettings = new SMTSettings(pdSettings,
		          piSettings, proof);
		    SolverLauncher launcher = new SolverLauncher(smtsettings);
		    launcher.addListener(new SolverLauncherListener() {
		       @Override
		       public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers) {
		    	   for (final SMTSolver solver : finishedSolvers) {
	    	            final SMTSolverResult.ThreeValuedTruth res = solver.getFinalResult().isValid();
	    	            
	    	            if (res == SMTSolverResult.ThreeValuedTruth.UNKNOWN) {
		    	               if(solver.getException() != null) {
		    	            	   solver.getException().printStackTrace();
		    	               }               
		    	            } else if (res == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE) {
		    	            	ModelExtractor query = solver.getSocket().getQuery();
		    	               if (query != null) {
		    	                  final Model m = solver.getSocket().getQuery()
		    	                          .getModel();
		    	                  System.out.println("obtained model");	  
		    	               } else {
		    	            	   System.out.println("query null");
		    	               		}
		    	            } else if (res == SMTSolverResult.ThreeValuedTruth.VALID) {         
		    	            }
		    	   }
		    	   System.out.println("launcher stopped");
		       }
		       
		       @Override
		       public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes, SolverLauncher launcher) {
		    	   System.out.println("launcher started");
		       }
		    });
		    // launcher.addListener(new SolverListener(settings));
		    final List<SolverType> solvers = new LinkedList<SolverType>();
//		    solvers.add(SolverType.Z3_CE_SOLVER);
//		    if (SolverType.Z3_CE_SOLVER.checkForSupport()) {
	    	solvers.add(SolverType.Z3_CE_SOLVER);
	    	SolverType.Z3_CE_SOLVER.isInstalled(true);	    	
		    launcher.launch(solvers, problems, proof.getServices());
			System.out.println("launcher launched");
			
			//Final result
			for (SMTProblem problem : problems) {
				SMTSolverResult result = problem.getFinalResult();
				System.out.println("result");
			}


			/* Z3 TEST ENDE
			*/
		    
		    
		    
		    
			// Hier m�chte ich jetzt eine Invariante generieren
			// Dazu 1. Java Code erstellen, der ausf�hrbar ist, um traces zu erhalten
			// Java Code als File abspeichern (warum? warum nicht einfach in memory)
			// FIXME innere Schleife behandeln (nicht nur first call)
			String javaCode = MethodGenerator.generateMethodFromKeYFormat(program, update, loop);
			
			//Write Code to file in workspace
			Path currentPath = Paths.get(System.getProperty("user.dir"));
			Path filePath = Paths.get(currentPath.toString(), "dynacode", "genmethod", "GeneratedMethod.java");
			writeStringToFile(javaCode, filePath.toString());
		}
	    
		Term suggestedInvariant	= keyAPI.getSuggestedInvariant(loop); // Erste (User angegebene) Loop Invariante: and(leq(Z(0(#)),r),equals(_x,javaAddInt(javaMulInt(q,_y),r)))<<SC>>
		return new Invariant(suggestedInvariant);
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

