package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.proof.init.AbstractInitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;

public class ABSInitConfig extends AbstractInitConfig {

    public ABSInitConfig(Profile profile) {
        super(profile);
    }

    @Override
    public IServices getServices() {
        return null;
    }

    @Override
    public ProofEnvironment getProofEnv() {
        return null;
    }

    @Override
    public AbstractInitConfig copy() {
        return null;
    }

}
