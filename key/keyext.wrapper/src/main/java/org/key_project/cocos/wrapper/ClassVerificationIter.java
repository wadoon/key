package org.key_project.cocos.wrapper;

import java.io.File;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.MiscTools;

public class ClassVerificationIter implements Iterable<Boolean> {
    KeYEnvironment<DefaultUserInterfaceControl> env;
    // List all specifications of classType in the source location
    final List<Contract> proofContracts = new LinkedList<Contract>();

    /**
     * Builds a symbolic execution tree for a given method
     * 
     * @param location       Path to the source code folder
     * @param className      Name of the class containing the method
     * @param classPaths     Optionally: Additional specifications for API classes
     * @param bootClassPath  Optionally: Different default specifications for Java
     *                       API
     * @param includes       Optionally: Additional includes to consider
     * @throws ProblemLoaderException Exception in loading method
     */
    public ClassVerificationIter(File location, String className, List<File> classPaths, File bootClassPath,
            List<File> includes) throws ProblemLoaderException {

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
        env = KeYEnvironment.load(location, classPaths, bootClassPath, includes);

        // Find class to verify
        KeYJavaType classType = env.getJavaInfo().getKeYJavaType(className);

        ImmutableSet<IObserverFunction> targets = env.getSpecificationRepository().getContractTargets(classType);
        for (IObserverFunction target : targets) {
            ImmutableSet<Contract> contracts = env.getSpecificationRepository().getContracts(classType, target);
            for (Contract contract : contracts) {
                if (!contract.isAuxiliary()) {
                    proofContracts.add(contract);
                }
            }
        }
        
//        Set<KeYJavaType> kjts = env.getJavaInfo().getAllKeYJavaTypes();
//        for (KeYJavaType type : kjts) {
//           if (!KeYTypeUtil.isLibraryClass(type)) {
//              ImmutableSet<IObserverFunction> targets1 = env.getSpecificationRepository().getContractTargets(type);
//              for (IObserverFunction target : targets1) {
//                 ImmutableSet<Contract> contracts = env.getSpecificationRepository().getContracts(type, target);
//                 for (Contract contract : contracts) {
//                    proofContracts.add(contract);
//                    System.out.println("Contract: '" + contract.getDisplayName() + "' of " + contract.getTarget() + " from " + type.getFullName() );
//                 }
//              }
//           }
//        }
        
        System.out.println("Number of contracts: " + proofContracts.toArray().length );
    }

    // FIXME Ensure always that all instances of KeYEnvironment are disposed
    public void dispose() {
        env.dispose();
    }


    @Override
    public Iterator<Boolean> iterator() {
        Iterator<Contract> proofContractIter = proofContracts.iterator();
        return new ClassVerificationIterator(env, proofContractIter);
    }

}
