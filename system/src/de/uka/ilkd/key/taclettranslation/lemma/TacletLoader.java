package de.uka.ilkd.key.taclettranslation.lemma;

import java.io.File;
import java.util.Collection;
import java.util.HashMap;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.lemmatagenerator.EnvironmentCreator;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.AbstractProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.io.IKeYFile;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.keyabs.po.ABSKeYUserProblemFile;

public abstract class TacletLoader<S extends IServices, IC extends AbstractInitConfig<S, IC>> {
        
        public abstract ImmutableSet<Taclet> loadAxioms();
        public abstract ImmutableSet<Taclet> loadTaclets();
        public abstract ImmutableSet<Taclet> getTacletsAlreadyInUse();
        
        protected IKeYFile<S, IC> tacletFile;
        protected final ProgressMonitor monitor;
        protected final ProblemInitializerListener<S,IC> listener;
        protected final Profile<S,IC>    profile;
        protected ProofEnvironment<IC> envForTaclets;
  
        public TacletLoader(ProgressMonitor monitor,
                        ProblemInitializerListener<S,IC> listener,
                        Profile<S,IC> profile) {
                super();
                this.monitor = monitor;
                this.listener = listener;
                this.profile = profile;
        }
        
    
        public IKeYFile<S, IC> getTacletFile() {
                return tacletFile;
        }


        public ProofEnvironment<IC> getProofEnvForTaclets() {
                if(envForTaclets == null){
                        try{
                                EnvironmentCreator<S,IC> ec = new EnvironmentCreator<S,IC>();
                        envForTaclets =  ec.create(PathConfig.getKeyConfigDir(), monitor, listener, profile); 
                          if(tacletFile == null){
                                  tacletFile = ec.getKeyFile();
                                           
                          }
                        }catch(Throwable e){
                                throw new RuntimeException(e);
                        }
                 }
                return envForTaclets;
        }
        
        
        public static class TacletFromFileLoader<S extends IServices, IC extends AbstractInitConfig<S, IC>> extends TacletLoader<S,IC>{
                private IC initConfig;
                private final File fileForDefinitions;
                private final File fileForTaclets;
                private final Collection<File> filesForAxioms;
                private final AbstractProblemInitializer<S, IC> problemInitializer;
                
           
           
               public TacletFromFileLoader(ProgressMonitor pm,
                                ProblemInitializerListener<S,IC> listener,
                                AbstractProblemInitializer<S,IC> problemInitializer,
                                Profile<S,IC> profile,
                                File fileForDefinitions, File fileForTaclets,
                                Collection<File> filesForAxioms,
                                ProofEnvironment<IC> env) {
                        super(pm,listener,profile);
                        this.fileForDefinitions = fileForDefinitions;
                        this.fileForTaclets = fileForTaclets;
                        this.filesForAxioms = filesForAxioms;
                        this.problemInitializer = problemInitializer;
                        this.envForTaclets = env;
                }
               
               public TacletFromFileLoader(TacletFromFileLoader<S,IC> loader, IC initConfig){
                       this(loader.monitor, loader.listener, loader.problemInitializer,loader.profile,
                            loader.fileForDefinitions,loader.fileForTaclets,loader.filesForAxioms,loader.envForTaclets,initConfig);
               }
               
               public TacletFromFileLoader(ProgressMonitor pm,
                               ProblemInitializerListener<S,IC> listener,
                               AbstractProblemInitializer<S,IC> problemInitializer,
                               Profile<S,IC> profile,
                               File fileForDefinitions, File fileForTaclets,
                               Collection<File> filesForAxioms,
                               ProofEnvironment<IC> env, IC config) {
                       this(pm,listener,problemInitializer,profile,fileForDefinitions,fileForTaclets,filesForAxioms,env);
                       this.initConfig = config;
               }
 

                public void prepare() {
                    IKeYFile<S,IC> keyFileDefs = (IKeYFile<S, IC>) (initConfig.getProfile() instanceof JavaProfile ?            
                                new KeYUserProblemFile("Definitions", fileForDefinitions, monitor)
                    :
                        new ABSKeYUserProblemFile("Definitions", fileForDefinitions, monitor));                    
                        try {
                                initConfig = problemInitializer.prepare(keyFileDefs);
                        } catch (ProofInputException e) {
                                throw new RuntimeException(e);
                        }
                }
                

       

                @Override
                public ImmutableSet<Taclet> loadTaclets() {
                        if(initConfig == null){
                                prepare();
                        }
                        tacletFile = 
                                (IKeYFile<S, IC>) (initConfig.getProfile() instanceof JavaProfile ? 
                                new KeYUserProblemFile(
                                        fileForTaclets.getName(), fileForTaclets, monitor) :
                                            new ABSKeYUserProblemFile(fileForTaclets.getName(), fileForTaclets, monitor));
                        
                        ;
                        return load(tacletFile, initConfig);
                        
                }
                
                @Override
                public ImmutableSet<Taclet> loadAxioms()
                                 {
                        if(initConfig == null){
                                prepare();
                        }
                        ImmutableSet<Taclet> axioms = DefaultImmutableSet.nil();
                        for (File f : filesForAxioms) {
                                IKeYFile<S,IC> keyFile = (IKeYFile<S, IC>) (initConfig.getProfile() instanceof JavaProfile ?
                                        new KeYUserProblemFile(
                                                f.getName(), f, monitor) :
                                                    new ABSKeYUserProblemFile(f.getName(), f, monitor)); 
                                ImmutableSet<Taclet> taclets = load(keyFile, initConfig);
                                getProofEnvForTaclets().registerRules(taclets,
                                                AxiomJustification.INSTANCE);
                                axioms = axioms.union(taclets);
                        }

                        return axioms;
                }  
                
               
                private IC createInitConfig(IC reference) {
                        IC newConfig = reference.copy();

                        newConfig.setTaclets(DefaultImmutableSet.<Taclet> nil());
                        newConfig.setTaclet2Builder(new HashMap<Taclet, TacletBuilder>());
                       
                        return newConfig;
                }

                
                private ImmutableSet<Taclet> load(IKeYFile<S,IC> keyFile,
                                IC reference) 
                                {
                        
                        // this ensures that necessary Java types are loaded
                        IC config = createInitConfig(reference);

                        keyFile.setInitConfig(config);
                        try{
                                keyFile.readRulesAndProblem();
                        }catch(Throwable e){
                                throw new RuntimeException(e);
                        }
                        return config.getTaclets();
                }




                @Override
                public IKeYFile<S, IC> getTacletFile() {
                       return tacletFile;
                }



                @Override
                public ImmutableSet<Taclet> getTacletsAlreadyInUse() {
                        return getProofEnvForTaclets().getInitConfig().getTaclets();
                }        
        }
        
        public static class KeYsTacletsLoader extends TacletLoader{


                
                

                public KeYsTacletsLoader(ProgressMonitor monitor,
                                ProblemInitializerListener listener,
                                Profile profile) {
                        super(monitor, listener, profile);
                }

                @Override
                public ImmutableSet<Taclet> loadAxioms() {
                        return DefaultImmutableSet.nil();
                }

                @Override
                public ImmutableSet<Taclet> loadTaclets() {
                        try {
                                getProofEnvForTaclets().registerRules( getProofEnvForTaclets().getInitConfig().getTaclets(), AxiomJustification.INSTANCE);                                    
                             return getProofEnvForTaclets().getInitConfig().getTaclets();             
                        } catch (Throwable e) {
                                throw new RuntimeException(e);
                        }
                        
                }
                



                @Override
                public ImmutableSet<Taclet> getTacletsAlreadyInUse() {
                        return DefaultImmutableSet.nil();
                }
                
        }
        


}
