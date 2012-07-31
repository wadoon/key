package de.uka.ilkd.keyabs.init;

import de.uka.ilkd.key.proof.init.AbstractInitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.proof.mgt.ABSProofEnvironment;

public class ABSInitConfig extends AbstractInitConfig {

    private ABSServices services;
    private ABSProofEnvironment env;

    public ABSInitConfig(ABSServices services, Profile profile) {
        super(profile);
        this.services = services;
        this.env = new ABSProofEnvironment(this);
    }

    @Override
    public ABSInitConfig copy() {
        ABSInitConfig ic = new ABSInitConfig(
                services.copyPreservesLDTInformation(), profile);
        super.initCopy(ic);
        return ic;
    }

    @Override
    public ABSProofEnvironment getProofEnv() {
        return env;
    }

    @Override
    public ABSServices getServices() {
        return services;
    }

}
