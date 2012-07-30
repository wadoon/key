package de.uka.ilkd.keyabs.init;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;

import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.init.AbstractProblemInitializer;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.IKeYFile;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.converter.ABSModelParserInfo;
import de.uka.ilkd.keyabs.init.io.ABSKeYFile;

public class ABSProblemInitializer extends
	AbstractProblemInitializer<ABSServices, ABSInitConfig> {

    public ABSProblemInitializer(ProgressMonitor mon, Profile profile,
	    boolean registerProof, ProblemInitializerListener listener) {
	this(mon, profile, (ABSServices) profile
		.createServices(new KeYRecoderExcHandler()), registerProof,
		listener);
    }

    public ABSProblemInitializer(ProgressMonitor mon, Profile profile,
	    ABSServices services, boolean registerProof,
	    ProblemInitializerListener listener) {
	super(mon, profile, services, registerProof, listener);
    }

    @Override
    protected IKeYFile createKeYFile(Includes in, String name) {
	return new ABSKeYFile(name, in.get(name), progMon);
    }

    @Override
    protected IKeYFile createTacletBaseKeYFile() {
	return new ABSKeYFile("taclet base", profile.getStandardRules()
		.getTacletBase(), progMon);
    }

    @Override
    protected void readJava(EnvInput envInput, ABSInitConfig initConfig)
	    throws ProofInputException {

	envInput.setInitConfig(initConfig);

	ABSModelParserInfo parserInfo = ((ABSServices) initConfig.getServices())
		.getProgramInfo().getABSParserInfo();

	String absPath = envInput.readJavaPath();
	JavaModel absModelDescription;
	if (absPath != null) {
	    String modelTag = "KeYABS_"
		    + new Long((new java.util.Date()).getTime());
	    absModelDescription = new JavaModel(absPath, modelTag,
		    new LinkedList<File>(), null);
	} else {
	    absModelDescription = JavaModel.NO_MODEL;
	}

	parserInfo.setup(absModelDescription);
	try {
	    parserInfo.readABSModel();
	} catch (IOException e) {
	    throw new ProofInputException(e);
	}

	initConfig.getProofEnv().setJavaModel(absModelDescription);
    }

    @Override
    protected void registerProgramDefinedSymbols(ABSInitConfig initConfig)
	    throws ProofInputException {

	// create and register program defined sorts
	final SortBuilder sb = new SortBuilder();
	sb.createAndRegisterSorts(initConfig);

	// create and register program defined or implied function symbols
	final FunctionBuilder fb = new FunctionBuilder();
	fb.createAndRegisterABSFunctions(initConfig);

	// create and register rules for function definitions
	//TODO
	

    }

}
