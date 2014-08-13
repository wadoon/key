package org.key_project.starvoors.util;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.Notation;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

public final class StaRVOOrSUtil {
   private StaRVOOrSUtil() {
   }
   
   public static void start(File location) throws ProofInputException, IOException {
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

   protected static void verify(KeYEnvironment<?> env, Contract contract) throws ProofInputException, IOException {
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
         env.getUi().startAndWaitForAutoMode(proof);
         // Update symbolic execution tree
         builder.analyse();
         // Analyze discovered symbolic execution tree
         analyzeSymbolicExecutionTree(builder, contract);
      }
      finally {
         env.getMediator().setProof(null);
         proof.dispose();
      }
   }
   
   protected static void analyzeSymbolicExecutionTree(SymbolicExecutionTreeBuilder builder, Contract contract) throws ProofInputException, IOException {
      System.out.println();
      System.out.println(contract.getName());
      String line = "";
      for (int i = 0; i < contract.getName().length();i++)
         line = line.concat("=");
      System.out.println(line);
           
      IExecutionStart symRoot = builder.getStartNode();
      ExecutionNodePreorderIterator iter = new ExecutionNodePreorderIterator(symRoot);
      Map<Term, ExecutionOperationContract> contractResults = new HashMap<Term, ExecutionOperationContract>();
      while (iter.hasNext()) {
         IExecutionNode next = iter.next();
         // Check applied contracts
         if (next instanceof ExecutionOperationContract) {
            ExecutionOperationContract ec = (ExecutionOperationContract)next;
            contractResults.put(ec.getResultTerm(), ec);
         }
         // Check if node is a leaf node
         if (next.getChildren().length == 0) {
            workWithLeafNode(next, contractResults);
         }
      }
   }
   
   protected static void workWithLeafNode(IExecutionNode leaf, final Map<Term, ExecutionOperationContract> contractResults) throws ProofInputException, IOException {
      // Check if verified
      boolean verified = leaf instanceof IExecutionTermination && ((IExecutionTermination)leaf).isBranchVerified();
      // Get path condition
      Term pathCondition = leaf.getPathCondition();
      StringBuffer sb = transformTermPP(pathCondition, contractResults, leaf.getServices());
      String pathConditionPP = sb.toString();
      System.out.println(leaf.getName() + " is " + leaf.getElementType() + " with path condition: " + pathConditionPP + " is verified = " + verified);
      System.out.println();
   }
   
   protected static StringBuffer transformTermPP(Term term, Map<Term, ExecutionOperationContract> contractResults, Services services) throws IOException {
      NotationInfo ni = new TransformationNotationInfo(services, contractResults);
      LogicPrinter logicPrinter = new LogicPrinter(new ProgramPrinter(null), ni, services, true);
      logicPrinter.getNotationInfo().refresh(services, true, false);
      logicPrinter.printTerm(term);
      return logicPrinter.result();      
   }
   
   protected static class TransformationNotationInfo extends NotationInfo {
      public TransformationNotationInfo(Services services, Map<Term, ExecutionOperationContract> contractResults) {
         setNotation(LocationVariable.class, new LocationVariableTransformationNotation(services, contractResults));
      }
   }
      
   protected static class LocationVariableTransformationNotation extends Notation.VariableNotation {
      private final Map<Term, ExecutionOperationContract> contractResults;
      
      private final Services services;

      protected LocationVariableTransformationNotation(Services services, Map<Term, ExecutionOperationContract> contractResults) {
         this.contractResults = contractResults;
         this.services = services;
      }

      @Override
      public void print(Term t, LogicPrinter sp) throws IOException {
         try {
            IExecutionOperationContract contract = contractResults.get(t);
            if (contract != null) {
               StringBuffer sb = new StringBuffer();
               FunctionalOperationContractImpl.appendMethodCallText(contract.getContractProgramMethod(), 
                                                                    contract.getResultTerm(), 
                                                                    contract.getResultTerm(), 
                                                                    originalParamVars, 
                                                                    services, 
                                                                    true, 
                                                                    false, 
                                                                    sb);
               sp.printConstant(sb.toString());
            }
            else {
               super.print(t, sp);
            }
         }
         catch (ProofInputException e) {
            throw new IOException(e);
         }
      }
   }
}