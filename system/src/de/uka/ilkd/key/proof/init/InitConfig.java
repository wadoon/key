// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;

/**
 * an instance of this class describes the initial configuration of the prover.
 * This includes sorts, functions, heuristics, and variables namespaces,
 * information on the underlying java model, and a set of rules.
 */
public class InitConfig extends AbstractInitConfig<Services, InitConfig> {

    /**
     * the services class allowing to access information about the underlying
     * program model
     */
    private final Services services;

        
    /**
     * the proof environment this init config belongs to
     */
    protected final ProofEnvironment<InitConfig> env;



    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public InitConfig(Services services, Profile<Services, InitConfig> profile) {
	super(profile);
        this.services  = services;
	this.env       = new ProofEnvironment<InitConfig>(this);
		
    }

           
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    /**
     * returns the proof environment using this initial configuration
     * @return the ProofEnvironment using this configuration
     */
    @Override
    public ProofEnvironment<InitConfig> getProofEnv() {
        assert env.getInitConfig() == this;
        return env;
    }

    @Override
    public InitConfig copy() {
        InitConfig ic = new InitConfig(services.copyPreservesLDTInformation(),
            profile);
        super.initCopy(ic);
        return ic;
    }
    
    /**
     * returns the Services of this initial configuration providing access
     * to the used program model
     * @return the Services of this initial configuration
     */
    @Override
    public Services getServices() {
        return services;
    }
}
