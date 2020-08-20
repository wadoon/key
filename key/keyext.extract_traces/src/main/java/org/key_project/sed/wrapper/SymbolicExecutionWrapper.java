package org.key_project.sed.wrapper;

import java.io.File;
import java.util.HashMap;
import java.util.List;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.MiscTools;

public class SymbolicExecutionWrapper {
	public SymbolicExecutionTreeBuilder builder;
	KeYEnvironment<DefaultUserInterfaceControl> env;
	
    /**
     * Builds a symbolic execution tree for a given method
     * @param location Path to the source code folder
     * @param className Name of the class containing the method
     * @param methodName Name of the method to symbolically execute
     * @param methodArgTypes An array of fully qualified names for each argument types,
     * e.g. "java.lang.String", "int[]" ...
     * @param precondition Optionally: JML precondition
     * @param classPaths Optionally: Additional specifications for API classes
     * @param bootClassPath Optionally: Different default specifications for Java API
     * @param includes Optionally: Additional includes to consider
     * @throws ProblemLoaderException Exception in loading method
     * @throws ProofInputException Exception in reading input
     */
    public SymbolicExecutionWrapper (
        File location,
        String className,
        String methodName,
        String[] methodArgTypes,
        String precondition,
        List<File> classPaths,
        File bootClassPath,
        List<File> includes
    ) throws ProblemLoaderException, ProofInputException {

        // Ensure that Taclets are parsed
        if (!ProofSettings.isChoiceSettingInitialised()) {
            KeYEnvironment<?> env
                = KeYEnvironment.load(location, classPaths, bootClassPath, includes);
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
        env = KeYEnvironment.load(profile, location, classPaths, bootClassPath, includes, true);

        // Find method to symbolically execute
        KeYJavaType classType = env.getJavaInfo().getKeYJavaType(className);
        ImmutableList<Type> signature = ImmutableSLList.<Type>nil();
        for (String t : methodArgTypes) {
            KeYJavaType keyType = env.getJavaInfo().getKeYJavaType(t);
            signature.append(keyType);
        }
        IProgramMethod pm
            = env.getJavaInfo().getProgramMethod(classType, methodName, signature, classType);

        // Instantiate proof for symbolic execution of the program method (Java semantics)
        AbstractOperationPO po = new ProgramMethodPO(env.getInitConfig(),
                                                     "Symbolic Execution of: " + pm,
                                                     pm,
                                                     precondition,
                                                     true,
                                                     true);

        Proof proof = env.createProof(po);
        // Create symbolic execution tree builder
        builder = new SymbolicExecutionTreeBuilder(proof,
                                                   false, // Merge branch conditions
                                                   false, // Use Unicode?
                                                   true, // Use Pretty Printing?
                                                   true, // Compute variables from updates
                                                   true); // Simplify conditions
        builder.analyse();
        // Optionally, create an SymbolicExecutionEnvironment
        // which provides access to all relevant objects for symbolic execution
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> symbolicEnv
            = new SymbolicExecutionEnvironment<DefaultUserInterfaceControl>(env, builder);
        // Configure strategy for full exploration
        SymbolicExecutionUtil.initializeStrategy(builder);
        SymbolicExecutionEnvironment
            .configureProofForSymbolicExecution(proof,
                                                100,
                                                false, // method contracts?
                                                false, // loop invariants?
                                                false, // block contracts?
                                                false, // hide branch labels?
                                                false); // alias checks?
        // Perform strategy which will stop at breakpoint
        symbolicEnv.getProofControl().startAndWaitForAutoMode(proof);
        builder.analyse();
    }
    
    /**
     * Prints the symbolic execution tree into the console.
     * @return number of leaves
     * @param returnValues compute and print the return values of a method
     * @throws ProofInputException Exception in reading input
     */
    public int printSymbolicExecutionTree(boolean returnValues) throws ProofInputException {
    	IExecutionStart startNode = builder.getStartNode();
    	return printSEDhierarchy(startNode, returnValues);
    }

    /**
     * Prints a symbolic execution sub tree to the console
     * @param node root of the sub tree
     * @return number of leaves
     * @param returnValues compute and print the return values of a method
     * @throws ProofInputException Exception in reading input
     */
    protected static int printSEDhierarchy (IExecutionNode<?> node, boolean returnValues) throws ProofInputException {
    	return printSEDhierarchy(node, 0, true, returnValues);
    }

    /**
     * Prints a symbolic execution sub tree to the console
     * @param node root of the sub tree
     * @param level start with 0, increment for each branch
     * @param plus true to print a + for branching
     * @param returnValues compute and print the return values of a method
     * @return number of leaves
     * @throws ProofInputException Exception in reading input
     */
    protected static int printSEDhierarchy (
    		IExecutionNode<?> node, int level, boolean plus, boolean returnValues
    		) throws ProofInputException {
    	int leaves = 0;

    	StringBuilder builder = new StringBuilder();
    	String name;
    	for(int i = 0; i < level; i++) {
    		builder.append("|  ");
        }
        if (plus) {
            builder.append("+ ");
            plus = false;
        } else {
            builder.append("| ");
        }
        if (returnValues && node instanceof IExecutionMethodReturn) {
            IExecutionMethodReturn mrNode = (IExecutionMethodReturn) node;
            name = (mrNode.isReturnValuesComputed() || !node.isDisposed())
                 ? mrNode.getNameIncludingReturnValue()
                 : node.getName();
            //builder.append( node.getPathCondition());

            //for (IExecutionConstraint constr : node.getConstraints()) {
            //    builder.append(constr);
            //}

        } else {
            name = node.getName();
//          name = node.toString();
        }
        // removes unnecessary << >> and \n (FIXME better solution)
        name = name.replaceAll("(<<.*?>>)|(«.*?»)", "");
        name = name.replaceAll("[\t ]*\n[\t ]*", " ");
        builder.append(name);
        System.out.println(builder);

        IExecutionNode<?>[] children = node.getChildren();
        if (children.length != 1) {
            level++;
            plus = true;
        }
        if (children.length == 0) {
        	leaves = 1;
        }
        for (IExecutionNode<?> child : node.getChildren()) {
            leaves += printSEDhierarchy(child, level, plus, returnValues);
        }
        return leaves;
    }


    // FIXME Ensure always that all instances of KeYEnvironment are disposed
    public void dispose() {
        env.dispose();
    }
    
}
