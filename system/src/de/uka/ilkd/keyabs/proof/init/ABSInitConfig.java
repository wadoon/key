package de.uka.ilkd.keyabs.proof.init;

import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.proof.mgt.ABSProofEnvironment;

public class ABSInitConfig extends InitConfig<ABSServices, ABSInitConfig>  {

    private ABSServices services;
    private ABSProofEnvironment env;

    public ABSInitConfig(ABSServices services, Profile<ABSServices, ABSInitConfig> profile) {
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
