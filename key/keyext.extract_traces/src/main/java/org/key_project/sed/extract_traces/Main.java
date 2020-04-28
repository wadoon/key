package org.key_project.sed.extract_traces;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.regex.Pattern;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.control.*;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.settings.*;
import de.uka.ilkd.key.symbolic_execution.*;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.util.*;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.proof.init.*;

/**
 * Example application which symbolically executes
 * {@code example/MaxIntBuggy}
 * Based on key.core.symbolic_execution.example
 * @author Lukas Grätz
 */
public class Main {
   /**
    * The program entry point.
    * @param args The start parameters.
    */
   public static void main(String[] args) {
      File location = new File("example"); // Path to the source code folder
      String className = "MaxIntBuggy";
      String methodName = "contentEqualsMax";
      String precondition
         =    "arr.length == 4 && arr[0] == 2 && arr[1] == 1 && arr[2] == 3 && arr[3] == 4"
         + "|| arr.length == 4 && arr[0] == 2 && arr[1] == 1 && arr[2] == 3 && arr[3] == 2"
         + "|| arr.length == 3 && arr[0] == 0 && arr[1] == 1 && arr[2] == 3";

      executeProcedure(location, className, methodName, precondition, null, null, null);
   }


   /**
    * Builds a SED tree for a method with zero arguments
    * @param location Path to the source code folder
    * @param className Name of the class containing the method
    * @param methodName Method name
    * @param precondition Optionally: JML precondition
    * @param classPaths Optionally: Additional specifications for API classes
    * @param bootClassPath Optionally: Different default specifications for Java API
    * @param includes Optionally: Additional includes to consider
    */
   public static void executeProcedure (File location, String className, String methodName, String precondition, List<File> classPaths, File bootClassPath, List<File> includes) {
      try {
         // Ensure that Taclets are parsed
         if (!ProofSettings.isChoiceSettingInitialised()) {
            KeYEnvironment<?> env = KeYEnvironment.load(location, classPaths, bootClassPath, includes);
            env.dispose();
         }
         // Set Taclet options
         ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
         HashMap<String, String> oldSettings = choiceSettings.getDefaultChoices();
         HashMap<String, String> newSettings = new HashMap<String, String>(oldSettings);
         newSettings.putAll(MiscTools.getDefaultTacletOptions());
         choiceSettings.setDefaultChoices(newSettings);
         // Load source code
         SymbolicExecutionJavaProfile profile = SymbolicExecutionJavaProfile.getDefaultInstance();
         KeYEnvironment<DefaultUserInterfaceControl> env =
               KeYEnvironment.load(profile, location, classPaths, bootClassPath, includes, true);
         try {
            // Find method to symbolically execute
            KeYJavaType classType = env.getJavaInfo().getKeYJavaType(className);
            ImmutableList<Type> signature = ImmutableSLList.<Type>nil();
            IProgramMethod pm = env.getJavaInfo().getProgramMethod(classType, methodName, signature, classType);
            // Instantiate proof for symbolic execution of the program method (Java semantics)
            AbstractOperationPO po = new ProgramMethodPO(env.getInitConfig(), 
                                                         "Symbolic Execution of: " + pm, 
                                                         pm, 
                                                         precondition,
                                                         true,  // Needs to be true for symbolic execution!
                                                         true); // Needs to be true for symbolic execution!
            // po = new ProgramMethodSubsetPO(...); // PO for symbolic execution of some statements within a method (Java semantics)
            // po = new FunctionalOperationContractPO(...) // PO for verification (JML semantics)
            Proof proof = env.createProof(po);
            // Create symbolic execution tree builder
            SymbolicExecutionTreeBuilder builder = new SymbolicExecutionTreeBuilder(proof, 
                                                                                    false, // Merge branch conditions 
                                                                                    false, // Use Unicode? 
                                                                                    true, // Use Pretty Printing? 
                                                                                    true, // Variables are collected from updates instead of the visible type structure 
                                                                                    true); // Simplify conditions
            builder.analyse();
            // Optionally, create an SymbolicExecutionEnvironment which provides access to all relevant objects for symbolic execution
            SymbolicExecutionEnvironment<DefaultUserInterfaceControl> symbolicEnv = new SymbolicExecutionEnvironment<DefaultUserInterfaceControl>(env, builder);
            // Configure strategy for full exploration
            SymbolicExecutionUtil.initializeStrategy(builder);
            SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, 
                                                                            100, 
                                                                            false,  // true to apply method contracts instead of inlining, 
                                                                            false,  // true to apply loop invariants instead of unrolling, 
                                                                            false,  // true to apply block contracts instead of expanding.
                                                                            false,  // true to hide branch conditions caused by symbolic execution within modalities not of interest, 
                                                                            false); // true to perform alias checks during symbolic execution
            // Perform strategy which will stop at breakpoint
            symbolicEnv.getProofControl().startAndWaitForAutoMode(proof);
            builder.analyse();
            printSymbolicExecutionTree("Finished Execution", builder);
         }
         finally {
            env.dispose(); // Ensure always that all instances of KeYEnvironment are disposed
         }
      }
      catch (Exception e) {
         System.out.println("Exception at '" + location + "':");
         e.printStackTrace();
      }
   }

   /**
    * Prints the symbolic execution tree into the console.
    * @param title The title.
    * @param builder The {@link SymbolicExecutionTreeBuilder} providing the root of the symbolic execution tree.
    * @throws ProofInputException 
    */
   protected static void printSymbolicExecutionTree(String title, SymbolicExecutionTreeBuilder builder) throws ProofInputException {
      System.out.println(title);
      System.out.println(StringUtil.createLine("=", title.length()));
      IExecutionStart startNode = builder.getStartNode();
      printSEDhierarchy(startNode, 0, true);
   }
   Pattern p = Pattern.compile("<<.*>>");

   /**
    * Prints the symbolic execution tree tree to the console
    * @param node root of the sub tree
    * @param level start with 0, increment for each branch
    * @param plus true to print a + for branching
    * @throws ProofInputException
    */
   protected static void printSEDhierarchy (IExecutionNode<?> node, int level, boolean plus) throws ProofInputException {
      StringBuilder builder = new StringBuilder();
      for(int i = 0; i < level; i++) {
         builder.append("|  ");
      }
      if (plus) {
         builder.append("+ ");
         plus = false;
      } else {
         builder.append("| ");
      }
      String name = node.getName();
      // removes unnecessary << >> and \n (FIXME better solution)
      name = name.replaceAll("(<<.*?>>)|\n","");
      builder.append(name);
      System.out.println(builder);

      IExecutionNode<?>[] children = node.getChildren();
      if (children.length != 1) {
         level++;
         plus = true;
      }
      for (IExecutionNode<?> child : node.getChildren()) {
         printSEDhierarchy(child, level, plus);
      }
   }
}
