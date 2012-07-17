package de.uka.ilkd.key.proof.init;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.LDTInput;
import de.uka.ilkd.key.proof.io.LDTInput.LDTInputListener;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.GlobalProofMgt;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleConfig;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.ProgressMonitor;

public abstract class AbstractProblemInitializer {

    public static interface ProblemInitializerListener{
        public void proofCreated(AbstractProblemInitializer sender, ProofAggregate proofAggregate);
        public void progressStarted(Object sender);
        public void progressStopped(Object sender);
        public void reportStatus(Object sender, String status, int progress);
        public void reportStatus(Object sender, String status);
        public void resetStatus(Object sender);
        public void reportException(Object sender, ProofOblInput input, Exception e);
    }

    protected abstract void registerProgramDefinedSymbols(AbstractInitConfig initConfig)
            throws ProofInputException;

    protected abstract void readJava(EnvInput envInput, AbstractInitConfig initConfig)
            throws ProofInputException;

    private static AbstractInitConfig baseConfig;
    protected final Profile profile;
    protected final IServices services;
    protected final ProgressMonitor progMon;
    private final HashSet<EnvInput> alreadyParsed = new LinkedHashSet<EnvInput>();
    protected final ProblemInitializerListener listener;
    protected final boolean registerProof;

    public AbstractProblemInitializer(ProgressMonitor mon, Profile profile,
            IServices services, boolean registerProof, ProblemInitializerListener listener) {
        this.profile = profile;
        this.services = services;
        this.progMon = mon;
        this.listener = listener;
        this.registerProof = registerProof;
    }

    /** 
     * displays the status report in the status line
     */
    protected void reportStatus(String status) {
        if(listener != null){
            listener.reportStatus(this,status);
        }
    
    }

    /** 
     * displays the status report in the status line 
     * and the maximum used by a progress bar
     * @param status the String to be displayed in the status line
     * @param progressMax an int describing what is 100 per cent
     */
    private void reportStatus(String status, int progressMax) {
        if(listener != null){
            listener.reportStatus(this,status,progressMax);
        }
    }

    /**
     * Helper for readIncludes().
     */
    private void readLDTIncludes(Includes in, AbstractInitConfig initConfig)
            throws ProofInputException {
                //avoid infinite recursion
                if(in.getLDTIncludes().isEmpty()) {
                    return;
                }
                
                //collect all ldt includes into a single LDTInput
                KeYFile[] keyFile = new KeYFile[in.getLDTIncludes().size()];
                
                int i = 0;
                for (String name : in.getLDTIncludes()) {
                    keyFile[i++] = new KeYFile(name, in.get(name), progMon);
                }
            
                LDTInput ldtInp = new LDTInput(keyFile, new LDTInputListener() {
                    @Override
                    public void reportStatus(String status, int progress) {
                	if(listener != null){
                	    listener.reportStatus(AbstractProblemInitializer.this, status, progress);
                	}		
                    }
                });
                
                //read the LDTInput
                readEnvInput(ldtInp, initConfig);
            }

    /**
     * Helper for readEnvInput().
     */
    private void readIncludes(EnvInput envInput, AbstractInitConfig initConfig)
            throws ProofInputException {
                envInput.setInitConfig(initConfig);
                
                Includes in = envInput.readIncludes();
                
                //read LDT includes
                readLDTIncludes(in, initConfig);
                
                //read normal includes
                for (String fileName : in.getIncludes()) {
                    KeYFile keyFile = new KeYFile(fileName, in.get(fileName), progMon);
                    readEnvInput(keyFile, initConfig);
                }
            }

    /**
     * Removes all schema variables, all generic sorts and all sort
     * depending symbols for a generic sort out of the namespaces.
     * Helper for readEnvInput().
     * 
     * See bug report #1185, #1189
     */
    private static void cleanupNamespaces(AbstractInitConfig initConfig) {
        Namespace newVarNS = new Namespace();	    
        Namespace newSortNS = new Namespace();
        Namespace newFuncNS = new Namespace();	    
        for(Named n : initConfig.sortNS().allElements()) {
            if(!(n instanceof GenericSort)) {
        	newSortNS.addSafely(n);
            }	
        }
        for(Named n : initConfig.funcNS().allElements()) {
            if(!(n instanceof SortDependingFunction 
        	    && ((SortDependingFunction)n).getSortDependingOn() 
        	    instanceof GenericSort)) {
        	newFuncNS.addSafely(n);
            }
        }
        //System.out.println(initConfig.funcNS().hashCode() + " ---> " + newFuncNS.hashCode());
        initConfig.getServices().getNamespaces().setVariables(newVarNS);
        initConfig.getServices().getNamespaces().setSorts(newSortNS);
        initConfig.getServices().getNamespaces().setFunctions(newFuncNS);
    }

    public final void readEnvInput(EnvInput envInput, AbstractInitConfig initConfig)
            throws ProofInputException {
                if(alreadyParsed.add(envInput)){
                    //read includes
                    if(!(envInput instanceof LDTInput)) {
                	readIncludes(envInput, initConfig);
                    }
                    
                    //sanity check
                    assert initConfig.varNS().allElements().size() == 0;
                    for(Named n : initConfig.sortNS().allElements()) {
                	assert n instanceof Sort && !(n instanceof GenericSort);
                    }	    
                    
                    //read envInput itself
                    reportStatus("Reading "+envInput.name(), 
                	    	 envInput.getNumberOfChars());
                    envInput.setInitConfig(initConfig);	    
                    envInput.read();	    
            
                    //clean namespaces
                    cleanupNamespaces(initConfig);	    	    
                }
            }

    private void populateNamespaces(Term term, NamespaceSet namespaces, Goal rootGoal) {
        for(int i = 0; i < term.arity(); i++) {
            populateNamespaces(term.sub(i), namespaces, rootGoal);
        }
        
        if(term.op() instanceof Function) {
            namespaces.functions().add(term.op());
        } else if(term.op() instanceof ProgramVariable) {
            final ProgramVariable pv = (ProgramVariable) term.op();
            if(namespaces.programVariables().lookup(pv.name()) == null) {
        	rootGoal.addProgramVariable((ProgramVariable)term.op());
            }
        } else if(term.op() instanceof ElementaryUpdate) {
            final ProgramVariable pv 
            	= (ProgramVariable)((ElementaryUpdate)term.op()).lhs();
            if(namespaces.programVariables().lookup(pv.name()) == null) {	    
        	rootGoal.addProgramVariable(pv);
            }
        } else if(term.javaBlock() != null && !term.javaBlock().isEmpty()) {
            final ProgramElement pe = term.javaBlock().program();
            final IServices serv = rootGoal.proof().getServices();
            final ImmutableSet<ProgramVariable> freeProgVars 
            	= MiscTools.getLocalIns(pe, serv)
            	           .union(MiscTools.getLocalOuts(pe, serv));
            for(ProgramVariable pv : freeProgVars) {
        	if(namespaces.programVariables().lookup(pv.name()) == null) {	    
        	    rootGoal.addProgramVariable(pv);
        	}		
            }
        }
    }

    /**
     * Ensures that the passed proof's namespaces contain all functions 
     * and program variables used in its root sequent.
     */
    private void populateNamespaces(Proof proof) {
        final NamespaceSet namespaces = proof.getNamespaces();
        final Goal rootGoal = proof.openGoals().head();
        Iterator<SequentFormula> it = proof.root().sequent().iterator();
        while(it.hasNext()) {
            SequentFormula cf = it.next();
            populateNamespaces(cf.formula(), namespaces, rootGoal);
        }
    }

    private AbstractInitConfig determineEnvironment(ProofOblInput po, AbstractInitConfig initConfig)
            throws ProofInputException {       
                ProofEnvironment env = initConfig.getProofEnv();
                
                //TODO: what does this actually do?
                ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().updateChoices(initConfig.choiceNS(), false);
                
                //init ruleConfig
                RuleConfig ruleConfig = new RuleConfig(initConfig.getActivatedChoices());
                env.setRuleConfig(ruleConfig);
                
                //register the proof environment
                //if(main != null) {
                 if(registerProof){
                    GlobalProofMgt.getInstance().registerProofEnvironment(env);
                }
            	               	
                return initConfig;
            }

    private void setUpProofHelper(ProofOblInput problem, ProofAggregate pl, AbstractInitConfig initConfig)
            throws ProofInputException {
                //ProofAggregate pl = problem.getPO();
                if(pl == null) {
                   throw new ProofInputException("No proof");
                }
                
                //register non-built-in rules	
                reportStatus("Registering rules");        
                initConfig.getProofEnv().registerRules(initConfig.getTaclets(), 
                				       AxiomJustification.INSTANCE);
            
                Proof[] proofs = pl.getProofs();
                for(int i = 0; i < proofs.length; i++) {
                    proofs[i].setNamespaces(proofs[i].getNamespaces());//TODO: refactor Proof.setNamespaces() so this becomes unnecessary
                    populateNamespaces(proofs[i]);
                }
                initConfig.getProofEnv().registerProof(problem, pl);
            
            }

    /**
     * Creates an initConfig / a proof environment and reads an EnvInput into it
     */
    public AbstractInitConfig prepare(EnvInput envInput) throws ProofInputException {
    if(listener != null){
        listener.progressStarted(this);
    }
    alreadyParsed.clear();
    
    //the first time, read in standard rules
    if(baseConfig == null || profile != baseConfig.getProfile()) {
        
        //ABSTODO: below should become a call to an abstract method createBaseConfig implemented by the subclasses to avoid the cast in 
        // createInitConfig
        baseConfig = profile.createInitConfig(services, profile);
    
        RuleSource tacletBase = profile.getStandardRules().getTacletBase();
        if(tacletBase != null) {
        	KeYFile tacletBaseFile
        	    = new KeYFile("taclet base", 
        		          profile.getStandardRules().getTacletBase(),
    		          progMon);
        	readEnvInput(tacletBaseFile, baseConfig);
        }	    
    }
      return prepare(envInput, baseConfig);
    
    }

    public AbstractInitConfig prepare(EnvInput envInput, AbstractInitConfig referenceConfig) throws ProofInputException {
        //create initConfig
         AbstractInitConfig initConfig = referenceConfig.copy();
        
        //register built in rules
        for(Rule r : profile.getStandardRules().getStandardBuiltInRules()) {
            initConfig.getProofEnv().registerRule(r, 
                    profile.getJustification(r));
        }
    
        //read Java
        readJava(envInput, initConfig);
    
        //register function and predicate symbols defined by Java program
        registerProgramDefinedSymbols(initConfig);
    
        //read envInput
        readEnvInput(envInput, initConfig);
    
        //done
        if(listener !=null){
           listener.progressStopped(this); 
        }
        return initConfig;
    }

    public Proof startProver(AbstractInitConfig initConfig, ProofOblInput po, int proofNum)
            throws ProofInputException {
                assert initConfig != null;
                if(listener!= null){
                    listener.progressStarted(this);
                }
                try {
                    //determine environment
                    initConfig = determineEnvironment(po, initConfig);
                   
                    //read problem
            	    reportStatus("Loading problem \"" + po.name() + "\"");
            	    po.readProblem();
            	    ProofAggregate pa = po.getPO();
            	    //final work
            	    setUpProofHelper(po, pa, initConfig);
            
                    //done
            	    if(listener != null){
                        listener.proofCreated(this, pa);
                    }
                  return pa.getProofs()[proofNum];
                       	    
                } catch (ProofInputException e) {    
                    if(listener != null){
                	listener.reportException(this, po, e);
                    }
                   
                    throw e;            
                } finally {
                    if(listener != null){
                	listener.progressStopped(this);
                    }
                           
                }    
            }

    public void startProver(ProofEnvironment env, ProofOblInput po)
            throws ProofInputException {
                assert env.getInitConfig().getProofEnv() == env;
                startProver(env.getInitConfig(), po, 0);
            }

    public void startProver(EnvInput envInput, ProofOblInput po)
            throws ProofInputException {
                try {
                    AbstractInitConfig initConfig = prepare(envInput);
                    startProver(initConfig, po, 0);
                } catch(ProofInputException e) {
                    reportStatus(envInput.name() + " failed");
                    throw e;
                }
            }

    public void tryReadProof(ProblemLoader prl, KeYUserProblemFile kupf)
            throws ProofInputException {
                reportStatus("Loading proof", kupf.getNumberOfChars());
                kupf.readProof(prl);
            }

}