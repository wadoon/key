package org.key_project.starvoors.util;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.starvoors.model.StaRVOOrSExecutionPath;
import org.key_project.starvoors.model.StaRVOOrSLoopInvariantApplication;
import org.key_project.starvoors.model.StaRVOOrSMethodContractApplication;
import org.key_project.starvoors.model.StaRVOOrSProof;
import org.key_project.starvoors.model.StaRVOOrSResult;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.PositionInfo;
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
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
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

// TODO: List contracts of API methods applied by proofs.
public final class StaRVOOrSUtil {
   private StaRVOOrSUtil() {
   }
   
   public static StaRVOOrSResult start(File location, 
                                       boolean ensureDefaultTacletOptions,
                                       boolean useOperationContracts,
                                       boolean useLoopInvarints) throws ProofInputException, IOException, ProblemLoaderException {
      if (ensureDefaultTacletOptions) {
         setDefaultTacletOptions(location);
      }
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
                     StaRVOOrSProof proofResult = verify(env, contract, useOperationContracts, useLoopInvarints);
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
   
   public static void setDefaultTacletOptions(File location) throws ProblemLoaderException {
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
   }

   protected static StaRVOOrSProof verify(KeYEnvironment<?> env, 
                                          Contract contract,
                                          boolean useOperationContracts,
                                          boolean useLoopInvarints) throws ProofInputException, IOException {
      InitConfig proofInitConfig = env.getInitConfig().deepCopy();
      ProofOblInput proofObligation = new FunctionalOperationContractPO(proofInitConfig, (FunctionalOperationContract)contract, true, true);
      Proof proof = env.getUi().createProof(proofInitConfig, proofObligation);
      try {
         // Configure symbolic execution settings used by the strategy of the auto mode
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
                                        useInfo.getNotFulfilledPreconditions(),
                                        useInfo.getNotFulfilledNullChecks(),
                                        useInfo.getNotInitiallyValidLoopInvariants(),
                                        useInfo.getNotPreservedLoopInvariants(),
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
       SpecificationUseInformation result = new SpecificationUseInformation();
       while (node != null) {
           if (node instanceof ExecutionOperationContract) {
               ExecutionOperationContract eoc = (ExecutionOperationContract) node;
               if (!eoc.isPreconditionComplied()) {
                   result.addNotFulfilledPrecondition(eoc);
               }
               if (eoc.hasNotNullCheck() && !eoc.isNotNullCheckComplied()) {
                  result.addNotFulfilledNullCheck(eoc);
               }
           }
           else if (node instanceof ExecutionLoopInvariant) {
               ExecutionLoopInvariant eli = (ExecutionLoopInvariant) node;
               if (!eli.isInitiallyValid()) {
                   result.addNotInitiallyValidLoopInvariant(eli);
               }
               if (!isLoopInvariantPreserved(eli)) {
                  result.addNotPreservedLoopInvariant(eli);
               }
           }
           node = node.getParent();
       }
       return result;
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
         return true; // The preserves branch is not available if KeY could close it completely meaning that the loop body is never executed.
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
      private final List<ExecutionOperationContract> notFulfilledPreconditions = new LinkedList<ExecutionOperationContract>();
       
      private final List<ExecutionOperationContract> notFulfilledNullChecks = new LinkedList<ExecutionOperationContract>();
       
      private final List<ExecutionLoopInvariant> notInitiallyValidLoopInvariants = new LinkedList<ExecutionLoopInvariant>();
      
      private final List<ExecutionLoopInvariant> notPreservedLoopInvariants = new LinkedList<ExecutionLoopInvariant>();

      public List<StaRVOOrSMethodContractApplication> getNotFulfilledPreconditions() {
         List<StaRVOOrSMethodContractApplication> result = new ArrayList<StaRVOOrSMethodContractApplication>();
         for (ExecutionOperationContract eoc : notFulfilledPreconditions) {
            result.add(toStaRVOOrSMethodContractApplication(eoc));
         }
         return result;
      }
      
      public List<StaRVOOrSMethodContractApplication> getNotFulfilledNullChecks() {
         List<StaRVOOrSMethodContractApplication> result = new ArrayList<StaRVOOrSMethodContractApplication>();
         for (ExecutionOperationContract eoc : notFulfilledNullChecks) {
            result.add(toStaRVOOrSMethodContractApplication(eoc));
         }
         return result;
      }
      
      protected StaRVOOrSMethodContractApplication toStaRVOOrSMethodContractApplication(ExecutionOperationContract eoc) {
         IExecutionNode<?> parent = eoc.getParent();
         while (parent instanceof IExecutionBranchCondition) {
            parent = parent.getParent();
         }
         PositionInfo info = parent != null ? parent.getActivePositionInfo() : null;
         return new StaRVOOrSMethodContractApplication(info != null ? info.getFileName() : null, 
                                                       info != null ? info.getStartPosition().getLine() : -1, 
                                                       info != null ? info.getStartPosition().getColumn() : -1, 
                                                       info != null ? info.getEndPosition().getLine() : -1, 
                                                       info != null ? info.getEndPosition().getColumn() : -1, 
                                                       eoc.getContractProgramMethod().getFullName(), 
                                                       eoc.getContract().getName());
      }
      
      public List<StaRVOOrSLoopInvariantApplication> getNotInitiallyValidLoopInvariants() {
         List<StaRVOOrSLoopInvariantApplication> result = new ArrayList<StaRVOOrSLoopInvariantApplication>();
         for (ExecutionLoopInvariant eli : notInitiallyValidLoopInvariants) {
            result.add(toStaRVOOrSLoopInvariantApplication(eli));
         }
         return result;
      }
      
      public List<StaRVOOrSLoopInvariantApplication> getNotPreservedLoopInvariants() {
         List<StaRVOOrSLoopInvariantApplication> result = new ArrayList<StaRVOOrSLoopInvariantApplication>();
         for (ExecutionLoopInvariant eli : notPreservedLoopInvariants) {
            result.add(toStaRVOOrSLoopInvariantApplication(eli));
         }
         return result;
      }

      protected StaRVOOrSLoopInvariantApplication toStaRVOOrSLoopInvariantApplication(ExecutionLoopInvariant eli) {
         PositionInfo info = eli.getLoopStatement().getGuardExpression().getPositionInfo();
         return new StaRVOOrSLoopInvariantApplication(info != null ? info.getFileName() : null, 
                                                      info != null ? info.getStartPosition().getLine() : -1, 
                                                      info != null ? info.getStartPosition().getColumn() : -1, 
                                                      info != null ? info.getEndPosition().getLine() : -1,
                                                      info != null ? info.getEndPosition().getColumn() : -1);
      }
      
      public void addNotFulfilledPrecondition(ExecutionOperationContract eoc) {
         assert eoc != null;
         notFulfilledPreconditions.add(eoc);
      }
      
      public void addNotFulfilledNullCheck(ExecutionOperationContract eoc) {
         assert eoc != null;
         notFulfilledNullChecks.add(eoc);
      }
      
      public void addNotInitiallyValidLoopInvariant(ExecutionLoopInvariant eli) {
         assert eli != null;
         notInitiallyValidLoopInvariants.add(eli);
      }
      
      public void addNotPreservedLoopInvariant(ExecutionLoopInvariant eli) {
         assert eli != null;
         notPreservedLoopInvariants.add(eli);
      }

      public boolean isAllPreconditionsFulfilled() {
         return notFulfilledPreconditions.isEmpty();
      }

      public boolean isAllNotNullChecksFulfilled() {
         return notFulfilledNullChecks.isEmpty();
      }

      public boolean isAllLoopInvariantsInitiallyFulfilled() {
         return notInitiallyValidLoopInvariants.isEmpty();
      }

      public boolean isAllLoopInvariantsPreserved() {
         return notPreservedLoopInvariants.isEmpty();
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