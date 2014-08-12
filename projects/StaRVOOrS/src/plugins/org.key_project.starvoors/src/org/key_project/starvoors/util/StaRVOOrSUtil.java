package org.key_project.starvoors.util;

import java.io.File;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.RuleKey;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ProofStarter;

public final class StaRVOOrSUtil {
   private StaRVOOrSUtil() {
   }
   
   public static void start(File location) throws ProofInputException {
      // Load source code and rules
      KeYEnvironment<?> env = KeYEnvironment.load(location, null, null);
//      KeYEnvironment<?> env = KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), location, null, null);
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
System.out.println("Handing: " + contract.getName());
      InitConfig proofInitConfig = env.getInitConfig().deepCopy();
      CustomUserInterface ui = new CustomUserInterface(false);
      ProofOblInput proofObligation = contract.createProofObl(proofInitConfig, contract);
      Proof proof = ui.createProof(proofInitConfig, proofObligation);
      try {
//         // Configure symbolic execution settings used by the strategy of the auto mode
//         boolean useOperationContracts = true;
//         boolean useLoopInvarints = true;
//         boolean nonExecutionBranchHidingSideProofs = false;
//         boolean aliasChecks = false; // May set to true to extend path conditions for aliasing checks
//         SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, 
//                                                                         ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN, 
//                                                                         useOperationContracts, 
//                                                                         useLoopInvarints, 
//                                                                         nonExecutionBranchHidingSideProofs, 
//                                                                         aliasChecks);
//         // Create symbolic execution tree which contains only the start node at beginning
//         SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(env.getMediator(), proof, false, false, false);
//         builder.analyse();
//         // Run auto mode
//         ui.startAndWaitForAutoMode(proof);
         OneStepSimplifier oss = MiscTools.findOneStepSimplifier(proof);
         if (oss != null) {
            oss.refresh(proof);
         }
//System.out.println("Proof: " + System.identityHashCode(oss));
//for (RuleKey o : proof.env().getJustifInfo().rule2justif.keySet()) {
//   if (o.r instanceof OneStepSimplifier) {
//System.out.println("InEnv: " + System.identityHashCode(o.r));
//   }
//}

         ProofStarter ps = new ProofStarter(false);
         ps.init(new SingleProof(proof, proofObligation.name()));
         ps.start(true);
         
         oss = MiscTools.findOneStepSimplifier(proof);
         if (oss != null) {
            oss.refresh(proof);
         }

//         // Update symbolic execution tree
//         builder.analyse();
//         // Print symbolic execution tree
//         System.out.println();
//         System.out.println(contract.getName());
//         System.out.println("==========================");
//         IExecutionStart symRoot = builder.getStartNode();
//         ExecutionNodePreorderIterator iter = new ExecutionNodePreorderIterator(symRoot);
//         while (iter.hasNext()) {
//            IExecutionNode next = iter.next();
//            if (next.getChildren().length == 0) {
//               System.out.println(next.getName() + " is " + next.getElementType());
//            }
//         }
      }
      finally {
//         env.getMediator().setProof(null);
         proof.dispose();
      }
   }

   private static InitConfig cloneEnvironment(KeYEnvironment<?> environment){
      InitConfig sourceInitConfig = environment.getInitConfig();
      // Create new InitConfig and initialize it with value from initial one.
      InitConfig initConfig = new InitConfig(environment.getServices().copy(environment.getProfile(), false));
      initConfig.setActivatedChoices(sourceInitConfig.getActivatedChoices());
      ProofSettings clonedSettings = sourceInitConfig.getSettings() != null ? new ProofSettings(sourceInitConfig.getSettings()) : null;
      initConfig.setSettings(clonedSettings);
      initConfig.setTaclet2Builder(sourceInitConfig.getTaclet2Builder());
      initConfig.setTaclets(sourceInitConfig.getTaclets());
      // Create new ProofEnvironment and initialize it with values from initial one.
      ProofEnvironment env = initConfig.getProofEnv();
      env.setJavaModel(sourceInitConfig.getProofEnv().getJavaModel());
      for (Taclet taclet : sourceInitConfig.activatedTaclets()) {
         env.getJustifInfo().addJustification(taclet, sourceInitConfig.getProofEnv().getJustifInfo().getJustification(taclet));
      }
      for (BuiltInRule rule : initConfig.builtInRules()) {
         RuleJustification origJusti = sourceInitConfig.getProofEnv().getJustifInfo().getJustification(rule);
         if (origJusti == null) {
            assert rule instanceof OneStepSimplifier;
            origJusti = AxiomJustification.INSTANCE;
         }
         env.getJustifInfo().addJustification(rule, origJusti);
      }
      return initConfig;
   }
}