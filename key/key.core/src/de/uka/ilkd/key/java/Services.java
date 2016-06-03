// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.java.recoderext.SchemaCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Counter;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.Debug;

/**
 * this is a collection of common services to the KeY prover. Services
 * include information on the underlying Java model and a converter to
 * transform Java program elements to logic (where possible) and back.
 */
public class Services implements TermServices {
   /**
     * the proof
     */
    private Proof proof;

    /**
     * proof specific namespaces (functions, predicates, sorts, variables)
     */
    private NamespaceSet namespaces = new NamespaceSet();

    /**
     * map of names to counters
     */
    private HashMap<String, Counter> counters;

    /**
     * specification repository
     */
    private SpecificationRepository specRepos;
    
    private NameRecorder nameRecorder;
    
    /** programming language dependent services like converting expressions, program type information etc. */
    private JavaServices javaServices;

    /** The profile specifies the logic that is used and provides specialised components */
    private final Profile profile;
    
    /** common used caches */
    private final ServiceCaches caches;
    
    /** term construction */
    private final TermBuilder termBuilder;

    /** contains all the specified theories (LDTs) */
    private TheoryServices theories;


    /**
     * creates a new Services object with a new TypeConverter and a new
     * JavaInfo object with no information stored at none of these.
     */
    public Services(Profile profile){
    	assert profile != null;
    	this.profile = profile;
    	this.counters = new LinkedHashMap<String, Counter>();
    	this.caches = new ServiceCaches();
        this.theories = new TheoryServices();
        this.termBuilder = new TermBuilder(new TermFactory(caches.getTermFactoryCache()), this);
    	this.specRepos = new SpecificationRepository(this);
        this.nameRecorder = new NameRecorder();
        
        this.javaServices = new JavaServices(this);
    }

    private Services(Profile profile, KeYCrossReferenceServiceConfiguration crsc, KeYRecoderMapping rec2key, 
    		HashMap<String, Counter> counters, ServiceCaches caches) {
    	assert profile != null;
    	assert counters != null;
    	assert caches != null;

    	this.profile = profile;
    	this.counters = counters;
    	this.caches = caches;
        this.theories     = new TheoryServices();
        this.termBuilder  = new TermBuilder(new TermFactory(caches.getTermFactoryCache()), this);
    	this.specRepos    = new SpecificationRepository(this);
        this.nameRecorder = new NameRecorder();
        
        this.javaServices = new JavaServices(this, crsc, rec2key);
    }


    public NameRecorder getNameRecorder() {
        return nameRecorder;
    }

    
    public void saveNameRecorder(Node n) {
        n.setNameRecorder(nameRecorder);
        nameRecorder = new NameRecorder();
    }

    
    public void addNameProposal(Name proposal) {
        nameRecorder.addProposal(proposal);
    }

    /** returns the theories of the logic */
    public TheoryServices getTheories() {
        return theories;
    }

    
    public SpecificationRepository getSpecificationRepository() {
        return specRepos;
    }
    
    /**
     * creates a new services object containing a copy of the java info of
     * this object and a new TypeConverter (shallow copy)
     * The copy does not belong to a {@link Proof} object and can hence be used for a new proof.
     * @param shareCaches {@code true} The created {@link Services} will use the same {@link ServiceCaches} like this instance; {@code false} the created {@link Services} will use a new empty {@link ServiceCaches} instance.
     * @return the copy
     */
    public Services copy(boolean shareCaches) {
       return copy(getProfile(), shareCaches);
    }

    /**
     * Creates a copy of this {@link Services} in which the {@link Profile} is replaced.
     * The copy does not belong to a {@link Proof} object and can hence be used for a new proof.
     * @param profile The new {@link Profile} to use in the copy of this {@link Services}.
     * @param shareCaches {@code true} The created {@link Services} will use the same {@link ServiceCaches} like this instance; {@code false} the created {@link Services} will use a new empty {@link ServiceCaches} instance.
     * @return The created copy.
     */
    public Services copy(Profile profile, boolean shareCaches) {
    	final KeYProgModelInfo keYProgModelInfo = javaServices.getJavaInfo().getKeYProgModelInfo();
        Debug.assertTrue
    	(!(keYProgModelInfo.getServConf() 
    			instanceof SchemaCrossReferenceServiceConfiguration),
    			"services: tried to copy schema cross reference service config.");
    	ServiceCaches newCaches = shareCaches ? caches : new ServiceCaches();
    	Services s = new Services
    			(profile, keYProgModelInfo.getServConf(), keYProgModelInfo.rec2key().copy(),
    					copyCounters(), newCaches);
    	s.specRepos = specRepos;
        s.setNamespaces(namespaces.copy());
        s.nameRecorder = nameRecorder.copy();

        s.theories.init(theories);
        s.javaServices.setTypeconverter(getJavaServices().getTypeConverter().copy(s));
    	s.javaServices.setJavaModel(getJavaServices().getJavaModel());
        return s;
    }
    
    /**
     * Creates a deep copy of {@link #counters} which means that a new
     * list is created with a copy of each contained {@link Counter}.
     * @return The created deep copy with new {@link Counter} instances.
     */
    private HashMap<String, Counter> copyCounters() {
       HashMap<String, Counter> result = new LinkedHashMap<String, Counter>();
       for (Entry<String, Counter> entry : counters.entrySet()) {
          result.put(entry.getKey(), entry.getValue().copy());
       }
       return result;
    }

    /**
     * creates a new service object with the same ldt information 
     * as the actual one
     */
    public Services copyPreservesLDTInformation() {
    	Debug.assertTrue
    	(!(getJavaServices().getJavaInfo().getKeYProgModelInfo().getServConf() 
    			instanceof SchemaCrossReferenceServiceConfiguration),
    			"services: tried to copy schema cross reference service config.");
        Services s = new Services(getProfile());
        s.setNamespaces(namespaces.copy());
        s.nameRecorder = nameRecorder.copy();
        
        s.theories.init(theories);
        s.javaServices.setTypeconverter(getJavaServices().getTypeConverter().copy(s));
    	s.javaServices.setJavaModel(getJavaServices().getJavaModel());
    	return s;
    }
    
    
    /** 
     * Marks this services as proof specific 
     * Please make sure that the {@link Services} does not not yet belong to an existing proof 
     * or that it is owned by a proof environment. In both cases copy the {@link InitConfig} via
     * {@link InitConfig#deepCopy()} or one of the other copy methods first. 
     * @param p_proof the Proof to which this {@link Services} instance belongs
     */
    public void setProof(Proof p_proof) {
       if (this.proof != null) {
          throw new IllegalStateException("Services are already owned by another proof:" + proof.name());
       }
       proof = p_proof;
    }
    
   
    public Services copyProofSpecific(Proof p_proof, boolean shareCaches) {
        ServiceCaches newCaches = shareCaches ? caches : new ServiceCaches();
        final Services s = new Services(getProfile(), getJavaServices().getJavaInfo().getKeYProgModelInfo().getServConf(), getJavaServices().getJavaInfo().getKeYProgModelInfo().rec2key(),
                copyCounters(), newCaches);
        s.proof = p_proof;
        s.specRepos = specRepos;
        s.setNamespaces(namespaces.copy());
        s.nameRecorder = nameRecorder.copy();

        s.theories.init(theories);
        s.javaServices.setTypeconverter(getJavaServices().getTypeConverter().copy(s));
        s.javaServices.setJavaModel(getJavaServices().getJavaModel());

        return s;
    }

    
    /*
     * returns an existing named counter, creates a new one otherwise
     */
    public Counter getCounter(String name) {
        Counter c = counters.get(name);
        if (c != null) return c;
        c = new Counter(name);
        counters.put(name, c);
        return c;
    }

    /**
     * returns the namespaces for functions, predicates etc.
     * @return the proof specific namespaces
     */
    @Override
    public NamespaceSet getNamespaces() {
        return namespaces;
    }
    
    
    /**
     * sets the namespaces of known predicates, functions, variables
     * @param namespaces the NamespaceSet with the proof specific namespaces
     */
    public void setNamespaces(NamespaceSet namespaces) {
        this.namespaces = namespaces;
    }
    
    
    /**
     * Returns the proof to which this object belongs, or null if it does not 
     * belong to any proof.
     */
    public Proof getProof() {
	return proof;
    }

    public interface ITermProgramVariableCollectorFactory{
       public TermProgramVariableCollector create(Services services);
    }

    /**
     * Returns the sued {@link Profile}.
     * @return The used {@link Profile}.
     */
    public Profile getProfile() {
        return profile;
    }
    
    /**
     * Returns the used {@link ServiceCaches}.
     * @return The used {@link ServiceCaches}.
     */
    public ServiceCaches getCaches() {
        return caches;
    }
    
    /**
     * Returns the {@link TermBuilder} used to create {@link Term}s.
     * @return The {@link TermBuilder} used to create {@link Term}s.
     */
    @Override
    public TermBuilder getTermBuilder() {
       return termBuilder;
    }

    /**
     * Returns the {@link TermFactory} used to create {@link Term}s.
     * @return The {@link TermFactory} used to create {@link Term}s.
     */
    @Override
    public TermFactory getTermFactory() {
        return termBuilder.tf();
    }

    public JavaServices getJavaServices() {
       return javaServices;
   }

}