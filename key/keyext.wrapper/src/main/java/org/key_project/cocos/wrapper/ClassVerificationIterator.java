package org.key_project.cocos.wrapper;

import java.util.Iterator;


import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;

public class ClassVerificationIterator implements Iterator<Boolean> {
    public ClassVerificationIterator(KeYEnvironment<DefaultUserInterfaceControl> env,
            Iterator<Contract> proofContractIter) {
        this.env = env;
        this.proofContractIter = proofContractIter;
    }

    KeYEnvironment<DefaultUserInterfaceControl> env;
    Iterator<Contract> proofContractIter;

    // FIXME Ensure always that all instances of KeYEnvironment are disposed
    public void dispose() {
        env.dispose();
    }

    @Override
    public boolean hasNext() {
        return proofContractIter.hasNext();
    }

    @Override
    public Boolean next() {
        boolean closed = false;
        Contract contract = proofContractIter.next();
        
        if (contract == null) {
            return null;
        }

        Proof proof = null;
        // Create proof
        try {
            proof = env.createProof(contract.createProofObl(env.getInitConfig(), contract));
            // Set proof strategy options
            StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
            sp.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_CONTRACT_EXTERNAL);
            sp.setProperty(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_ON);
            sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_ON);
            sp.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
            sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
            proof.getSettings().getStrategySettings().setActiveStrategyProperties(sp);
            // Make sure that the new options are used
            int maxSteps = 10000;
            ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(maxSteps);
            ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(sp);
            proof.getSettings().getStrategySettings().setMaxSteps(maxSteps);
            proof.setActiveStrategy(proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, sp));
            // Start auto mode
            env.getUi().getProofControl().startAndWaitForAutoMode(proof);
            // Show proof result
            closed = proof.openGoals().isEmpty();
            System.out.println("Contract '" + contract.getDisplayName() + "' of " + contract.getTarget() + " is "
                    + (closed ? "verified" : "still open") + ".");
        } catch (ProofInputException e) {
            System.out.println("Exception at '" + contract.getDisplayName() + "' of " + contract.getTarget() + ":");
            e.printStackTrace();
        } finally {
            if (proof != null) {
                proof.dispose(); // Ensure always that all instances of Proof are disposed
            }
        }

        return new Boolean(closed);
    }

}
