package org.key_project.starvoors.util;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.key_project.starvoors.model.StaRVOOrSExecutionPath;
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.Notation;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination.TerminationKind;
import de.uka.ilkd.key.symbolic_execution.model.impl.AbstractExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.KeYTypeUtil;

public final class StaRVOOrSUtil {
   private StaRVOOrSUtil() {
   }
   
   public static StaRVOOrSResult start(File location) throws ProofInputException, IOException, ProblemLoaderException {
      // Ensure that Taclets are parsed
      if (!ProofSettings.isChoiceSettingInitialised()) {
         KeYEnvironment<?> env = KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), location, null, null, null, true);
         env.dispose();
      }
      // Set Taclet options
      ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
      HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
      HashMap<String, String> newSettings = new HashMap<String, String>(oldSettings);
      newSettings.putAll(SymbolicExecutionUtil.getDefaultTacletOptions());
      choiceSettings.setDefaultChoices(newSettings);
      // Load source code and rules
      KeYEnvironment<?> env = KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), location, null, null, null, true);
      try {
         StaRVOOrSResult result = new StaRVOOrSResult();
         // Iterate over available types to list proof obligations
         Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
         for (KeYJavaType type : kjts) {
            if (!KeYTypeUtil.isLibraryClass(type)) {
               ImmutableSet<IObserverFunction> targets = env.getSpecificationRepository().getContractTargets(type);
               for (IObserverFunction target : targets) {
                  ImmutableSet<Contract> contracts = env.getSpecificationRepository().getContracts(type, target);
                  for (Contract contract : contracts) {
                     StaRVOOrSProof proofResult = verify(env, contract);
                     if (proofResult != null) {
                        result.addProof(proofResult);
                     }
                  }
               }
            }
         }
         return result;
      }
      finally {
         env.dispose();
      }
   }

   protected static StaRVOOrSProof verify(KeYEnvironment<?> env, Contract contract) throws ProofInputException, IOException {
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
         SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(proof, false, false, true, false);
         builder.analyse();
         // Run auto mode
         env.getProofControl().startAndWaitForAutoMode(proof);
         // Update symbolic execution tree
         builder.analyse();
         // Analyze discovered symbolic execution tree
         StaRVOOrSProof proofResult = new StaRVOOrSProof(contract.getName(), contract.getPlainText(builder.getProof().getServices()));
         analyzeSymbolicExecutionTree(builder, contract, proofResult);
         return proofResult;
      }
      finally {
         proof.dispose();
      }
   }

   protected static void analyzeSymbolicExecutionTree(SymbolicExecutionTreeBuilder builder, Contract contract, StaRVOOrSProof proofResult) throws ProofInputException, IOException {
      System.out.println();
      System.out.println(contract.getName());
      String line = StringUtil.createLine("=", contract.getName().length());
      System.out.println(line);
      System.out.println(contract.getPlainText(builder.getProof().getServices()));
      System.out.println(line);

      Map<LocationVariable, ProgramVariable> preStateMapping = getPreStateMapping(builder.getProof());
      
      IExecutionStart symRoot = builder.getStartNode();
      ExecutionNodePreorderIterator iter = new ExecutionNodePreorderIterator(symRoot);
      Map<Term, ExecutionOperationContract> contractResults = new HashMap<Term, ExecutionOperationContract>();
      while (iter.hasNext()) {
         IExecutionNode<?> next = iter.next();
         // Check applied contracts
         if (next instanceof ExecutionOperationContract) {
            ExecutionOperationContract ec = (ExecutionOperationContract)next;
            contractResults.put(ec.getResultTerm(), ec);
         }
         // Check if node is a leaf node
         if (isLeaf(next)) {
            StaRVOOrSExecutionPath path = workWithLeafNode(next, contractResults, preStateMapping);
            if (path != null) {
               proofResult.addPath(path);
            }
         }
      }
   }
   
   protected static boolean isLeaf(IExecutionNode<?> node) {
      return node.getChildren().length == 0;
   }
   
   protected static Map<LocationVariable, ProgramVariable> getPreStateMapping(Proof proof) {
      ContractPO po = proof.getServices().getSpecificationRepository().getPOForProof(proof);
      if (po instanceof AbstractOperationPO) {
         return ((AbstractOperationPO) po).getCurrentLocationToPreStateMapping();
      }
      else {
         return null;
      }
   }
   
   protected static StaRVOOrSExecutionPath workWithLeafNode(IExecutionNode<?> leaf, final Map<Term, ExecutionOperationContract> contractResults, final Map<LocationVariable, ProgramVariable> preStateMapping) throws ProofInputException, IOException {
      // Check if verified
      boolean verified = isVerified(leaf);
      SpecificationUseInformation useInfo = computeSpecificationUseInformation(leaf);
      // Get path condition
      Term pathCondition = leaf.getPathCondition();
      StringBuffer sb = transformTermPP(pathCondition, contractResults, preStateMapping, leaf.getServices());
      String pathConditionPP = sb.toString();
      System.out.println(leaf.getName() + " is " + leaf.getElementType() + " with path condition: " + pathConditionPP + " is verified = " + verified + " (" + useInfo + ")");
      System.out.println();
      return new StaRVOOrSExecutionPath(pathConditionPP.trim(), 
                                        verified,
                                        useInfo.isAllPreconditionsFulfilled(),
                                        useInfo.isAllNotNullChecksFulfilled(),
                                        useInfo.isAllLoopInvariantsInitiallyFulfilled(),
                                        useInfo.isAllLoopInvariantsPreserved(),
                                        getTerminationKind(leaf));
   }
   
   protected static TerminationKind getTerminationKind(IExecutionNode<?> node) {
      return node instanceof IExecutionTermination ?
             ((IExecutionTermination) node).getTerminationKind() :
             null;
   }

   protected static boolean isVerified(IExecutionNode<?> node) {
      return node instanceof IExecutionTermination && ((IExecutionTermination) node).isBranchVerified();
   }
   
   protected static SpecificationUseInformation computeSpecificationUseInformation(IExecutionNode<?> node) {
       boolean allPreconditionsFulfilled = true;
       boolean allNotNullChecksFulfilled = true;
       boolean allLoopInvariantsInitiallyFulfilled = true;
       boolean allLoopInvariantsPreserved = true;
       while (node != null &&
              (allPreconditionsFulfilled || allNotNullChecksFulfilled || allLoopInvariantsInitiallyFulfilled)) {
           if (node instanceof ExecutionOperationContract) {
               ExecutionOperationContract eoc = (ExecutionOperationContract) node;
               if (!eoc.isPreconditionComplied()) {
                   allPreconditionsFulfilled = false;
               }
               if (eoc.hasNotNullCheck() && !eoc.isNotNullCheckComplied()) {
                  allNotNullChecksFulfilled = false;
               }
           }
           else if (node instanceof ExecutionLoopInvariant) {
               ExecutionLoopInvariant eli = (ExecutionLoopInvariant) node;
               if (!eli.isInitiallyValid()) {
                   allLoopInvariantsInitiallyFulfilled = false;
               }
               if (allLoopInvariantsPreserved && !isLoopInvariantPreserved(eli)) {
                  allLoopInvariantsPreserved = false;
               }
           }
           node = node.getParent();
       }
       return new SpecificationUseInformation(allPreconditionsFulfilled, 
                                              allNotNullChecksFulfilled, 
                                              allLoopInvariantsInitiallyFulfilled, 
                                              allLoopInvariantsPreserved);
   }
   
   private static boolean isLoopInvariantPreserved(ExecutionLoopInvariant eli) {
      IExecutionNode<?> preservesBranch = getBodyPreservesInvariantBranchCondition(eli);
      if (preservesBranch != null) {
         boolean preserved = true;
         ExecutionNodePreorderIterator iter = new ExecutionNodePreorderIterator(preservesBranch);
         while (preserved && iter.hasNext()) {
            IExecutionNode<?> next = iter.next();
            if (isLeaf(next) && !isVerified(next)) {
               preserved = false;
            }
         }
         return preserved;
      }
      else {
         return true; // The preseres branch is not avialable if KeY could close it completely meaning that the loop body is never executed.
      }
   }
   
   private static IExecutionNode<?> getBodyPreservesInvariantBranchCondition(ExecutionLoopInvariant eli) {
      return ArrayUtil.search(eli.getChildren(), new IFilter<AbstractExecutionNode<?>>() {
         @Override
         public boolean select(AbstractExecutionNode<?> element) {
            return element instanceof ExecutionBranchCondition &&
                   "Body Preserves Invariant".equals(((ExecutionBranchCondition) element).getAdditionalBranchLabel());
         }
      });
   }

   private static class SpecificationUseInformation {
      private final boolean allPreconditionsFulfilled;
       
      private final boolean allNotNullChecksFulfilled;
       
      private final boolean allLoopInvariantsInitiallyFulfilled;
      
      private final boolean allLoopInvariantsPreserved;

      public SpecificationUseInformation(boolean allPreconditionsFulfilled, 
                                         boolean allNotNullChecksFulfilled, 
                                         boolean allLoopInvariantsInitiallyFulfilled, 
                                         boolean allLoopInvariantsPreserved) {
         this.allPreconditionsFulfilled = allPreconditionsFulfilled;
         this.allNotNullChecksFulfilled = allNotNullChecksFulfilled;
         this.allLoopInvariantsInitiallyFulfilled = allLoopInvariantsInitiallyFulfilled;
         this.allLoopInvariantsPreserved = allLoopInvariantsPreserved;
      }

      public boolean isAllPreconditionsFulfilled() {
         return allPreconditionsFulfilled;
      }

      public boolean isAllNotNullChecksFulfilled() {
         return allNotNullChecksFulfilled;
      }

      public boolean isAllLoopInvariantsInitiallyFulfilled() {
         return allLoopInvariantsInitiallyFulfilled;
      }

      public boolean isAllLoopInvariantsPreserved() {
         return allLoopInvariantsPreserved;
      }

      @Override
      public String toString() {
         return "all preconditions fulfilled = " + isAllPreconditionsFulfilled() +
                ", all not null checks fulfilled = " + isAllNotNullChecksFulfilled() +
                ", all loop invariants initially fulfilled = " + isAllLoopInvariantsInitiallyFulfilled() +
                ", all loop invariants preserved = " + isAllLoopInvariantsPreserved();
      }
   }
   
   protected static StringBuffer transformTermPP(Term term, Map<Term, ExecutionOperationContract> contractResults, Map<LocationVariable, ProgramVariable> preStateMapping, Services services) throws IOException {
      NotationInfo ni = new TransformationNotationInfo(services, contractResults, preStateMapping);
      LogicPrinter logicPrinter = new LogicPrinter(new ProgramPrinter(null), ni, services, true);
      logicPrinter.getNotationInfo().refresh(services, true, false);
      logicPrinter.printTerm(term);
      return logicPrinter.result();      
   }
   
   private static class TransformationNotationInfo extends NotationInfo {
       private final Services services;
       
       private final Map<Term, ExecutionOperationContract> contractResults;
       
       private final Map<LocationVariable, ProgramVariable> preStateMapping;
       
       public TransformationNotationInfo(Services services, Map<Term, 
                                         ExecutionOperationContract> contractResults, 
                                         Map<LocationVariable, ProgramVariable> preStateMapping) {
           this.services = services;
           this.contractResults = contractResults;
           this.preStateMapping = preStateMapping;
       }

       @Override
       protected HashMap<Object, Notation> createDefaultNotation() {
           HashMap<Object, Notation> notation = super.createDefaultNotation();
           updateNotation(notation);
           return notation;
       }

       @Override
       protected HashMap<Object, Notation> createPrettyNotation(Services services) {
           HashMap<Object, Notation> notation = super.createPrettyNotation(services);
           updateNotation(notation);
           return notation;
       }

       @Override
       protected HashMap<Object, Notation> createUnicodeNotation(Services services) {
           HashMap<Object, Notation> notation = super.createUnicodeNotation(services);
           updateNotation(notation);
           return notation;
       }
       
       protected void updateNotation(HashMap<Object, Notation> notation) {
           notation.put(LocationVariable.class, new LocationVariableTransformationNotation(services, contractResults, preStateMapping));
       }
   }
      
   protected static class LocationVariableTransformationNotation extends Notation.VariableNotation {
      private final Map<Term, ExecutionOperationContract> contractResults;
      
      private final Map<LocationVariable, ProgramVariable> preStateMapping;
      
      private final Services services;

      protected LocationVariableTransformationNotation(Services services, Map<Term, ExecutionOperationContract> contractResults, Map<LocationVariable, ProgramVariable> preStateMapping) {
         this.contractResults = contractResults;
         this.preStateMapping = preStateMapping;
         this.services = services;
      }

      @Override
      public void print(Term t, LogicPrinter sp) throws IOException {
         try {
            IExecutionOperationContract contract = contractResults.get(t);
            if (contract != null) {
               StringBuffer sb = new StringBuffer();
               ProgramVariable originalSelfVar = contract.getSelfTerm() != null ? (ProgramVariable)contract.getSelfTerm().op() : null;
               appendMethodCallText(contract.getContractProgramMethod(), 
                                    originalSelfVar, 
                                    contract.getContractParams(), 
                                    services, 
                                    true, 
                                    false, 
                                    sb);
               sp.printConstant(sb.toString());
            }
            else {
               IProgramVariable programVariable = preStateMapping.get(t.op());
               if (programVariable != null) {
                  sp.printConstant(programVariable.name().toString());
               }
               else {
                  super.print(t, sp);
               }
            }
         }
         catch (ProofInputException e) {
            throw new IOException(e);
         }
      }
      
      protected void appendMethodCallText(IProgramMethod pm,
                                          ProgramVariable originalSelfVar,
                                          ImmutableList<? extends SVSubstitute> originalParamVars,
                                          Services services, 
                                          boolean usePrettyPrinting,
                                          boolean useUnicodeSymbols, 
                                          final StringBuffer sig) throws IOException {
           if (!pm.isStatic() && !pm.isConstructor()) {
               sig.append(originalSelfVar);
               sig.append(".");
           }
           sig.append(pm.getName());
           sig.append("(");
           for (SVSubstitute subst : originalParamVars) {
              if (subst instanceof Named) {
                 Named named = (Named)subst;
                 sig.append(named.name()).append(", ");
              }
              else if (subst instanceof Term) {
                 StringBuffer paramText = transformTermPP((Term)subst, contractResults, preStateMapping, services);
                 sig.append(paramText.toString().trim()).append(", ");
              }
              else {
                 sig.append(subst).append(", ");
              }
           }
           if (!originalParamVars.isEmpty()) {
               sig.setLength(sig.length() - 2);
           }
           sig.append(")");
      }
   }
}