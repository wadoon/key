package org.key_project.starvoors.util;

import java.io.File;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.ProofStarter;

public final class StaRVOOrSUtil {
   private StaRVOOrSUtil() {
   }
   
   public static void start(File location) throws ProofInputException {
      // Load source code and rules
      KeYEnvironment<?> env = KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), location, null, null);
      try {
         // Iterate over available types to list proof obligations
         Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
         for (KeYJavaType type : kjts) {
            if (!KeYTypeUtil.isLibraryClass(type)) {
               ImmutableSet<IObserverFunction> targets = env.getSpecificationRepository().getContractTargets(type);
               for (IObserverFunction target : targets) {
                  ImmutableSet<Contract> contracts = env.getSpecificationRepository().getContracts(type, target);
                  for (Contract contract : contracts) {
                     verify(env, contract);
                  }
               }
            }
         }
      }
      finally {
         env.dispose();
      }
   }

   protected static void verify(KeYEnvironment<?> env, Contract contract) throws ProofInputException {
      InitConfig proofInitConfig = env.getInitConfig().deepCopy();
      ProofOblInput proofObligation = new FunctionalOperationContractPO(proofInitConfig, (FunctionalOperationContract)contract, true, true);
      Proof proof = env.getUi().createProof(proofInitConfig, proofObligation);
      try {
         // Configure symbolic execution settings used by the strategy of the auto mode
         boolean useOperationContracts = true;
         boolean useLoopInvarints = true;
         boolean nonExecutionBranchHidingSideProofs = false;
         boolean aliasChecks = false; // May set to true to extend path conditions for aliasing checks
         SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, 
                                                                         ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN, 
                                                                         useOperationContracts, 
                                                                         useLoopInvarints, 
                                                                         nonExecutionBranchHidingSideProofs, 
                                                                         aliasChecks);
         // Create symbolic execution tree which contains only the start node at beginning
         SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(env.getMediator(), proof, false, false, true);
         builder.analyse();
         // Run auto mode
         ProofStarter ps = new ProofStarter(false);
         ps.init(new SingleProof(proof, proofObligation.name()));
         ps.start();
         // Update symbolic execution tree
         builder.analyse();
         // Analyze discovered symbolic execution tree
         analyzeSymbolicExecutionTree(builder, contract);
      }
      finally {
         proof.dispose();
      }
   }
   
   protected static void analyzeSymbolicExecutionTree(SymbolicExecutionTreeBuilder builder, Contract contract) throws ProofInputException {
      System.out.println();
      System.out.println(contract.getName());
      System.out.println("==========================");
      IExecutionStart symRoot = builder.getStartNode();
      ExecutionNodePreorderIterator iter = new ExecutionNodePreorderIterator(symRoot);
      while (iter.hasNext()) {
         IExecutionNode next = iter.next();
         // Check if node is a leaf node
         if (next.getChildren().length == 0) {
            // Check if verified
            if (next instanceof IExecutionTermination && 
                ((IExecutionTermination)next).isBranchVerified()) {
               // Nothing to do
            }
            else {
               // Get path condition
               Term pathCondition = next.getPathCondition();
               // Pretty print path condition
               String pathConditionPP = next.getFormatedPathCondition();
               System.out.println(next.getName() + " is " + next.getElementType() + " with path condition: " + pathConditionPP);
            }
         }
      }
   }
   
   public static String prettyPrint(SymbolicExecutionTreeBuilder builder, Term term) {
      return SymbolicExecutionUtil.formatTerm(term, builder.getProof().getServices(), false, true);
   }
}