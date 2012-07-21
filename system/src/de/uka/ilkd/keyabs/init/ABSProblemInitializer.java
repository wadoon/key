package de.uka.ilkd.keyabs.init;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.LinkedList;

import abs.frontend.ast.DataConstructor;
import abs.frontend.ast.List;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.init.AbstractInitConfig;
import de.uka.ilkd.key.proof.init.AbstractProblemInitializer;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.IKeYFile;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.keyabs.abs.ABSInfo;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.converter.ABSModelParserInfo;
import de.uka.ilkd.keyabs.init.io.ABSKeYFile;

public class ABSProblemInitializer extends AbstractProblemInitializer {

    public ABSProblemInitializer(ProgressMonitor mon,
            Profile profile, 
            boolean registerProof,
            ProblemInitializerListener listener) {
        this(mon, profile, 
                profile.createServices(new KeYRecoderExcHandler()), 
                registerProof, listener);
    }

    public ABSProblemInitializer(ProgressMonitor mon, Profile profile,
            IServices services, boolean registerProof,
            ProblemInitializerListener listener) {
        super(mon, profile, services, registerProof, listener);
    }


    @Override
    protected IKeYFile createKeYFile(Includes in, String name) {
        return new ABSKeYFile(name, in.get(name), progMon);
    }

    @Override
    protected IKeYFile createTacletBaseKeYFile() {
        return new ABSKeYFile("taclet base", 
                profile.getStandardRules().getTacletBase(),
                progMon);
    }

    @Override
    protected void readJava(EnvInput envInput, AbstractInitConfig initConfig)
            throws ProofInputException {
        ABSModelParserInfo parserInfo = ((ABSServices)initConfig.getServices()).getProgramInfo().getABSParserInfo();

        String modelTag = "KeYABS_" + new Long((new java.util.Date()).getTime());
        JavaModel absModelDescription = new JavaModel("/Users/bubel/tmp/testabs/", modelTag, new LinkedList<File>(), null);

        parserInfo.setup(absModelDescription);
        try {
            parserInfo.readABSModel();
        } catch (IOException e) {
            throw new ProofInputException(e);
        }

        parserInfo.finish(initConfig.getServices());



        initConfig.getProofEnv().setJavaModel(absModelDescription);

    }

    @Override
    protected void registerProgramDefinedSymbols(AbstractInitConfig initConfig)
            throws ProofInputException {

        ABSInfo info = (ABSInfo) initConfig.getServices().getProgramInfo();

        System.out.println("Registering Sorts (" + info.getAllKeYJavaTypes().size() + ")" );
        //register sorts
        for (KeYJavaType t : info.getAllKeYJavaTypes()) {
            if (initConfig.sortNS().lookup(t.getSort().name()) == null) {
                initConfig.sortNS().addSafely(t.getSort());
            } else {
                System.out.println(getClass() + ": Skipping "+t.getFullName());
            }
        
        }


        System.out.println("Registering Functions");

        // test code
        for (List<DataConstructor> constructors  : info.getABSParserInfo().getDataTypes2dataConstructors().values()) {
            for (DataConstructor c : constructors) {
                System.out.println("" + c.getName() + ":" + c.getConstructorArgs());

                Sort intS = initConfig.getServices().getTypeConverter().getIntegerLDT().targetSort();

                Sort[] argSorts = new Sort[c.getConstructorArgList().getNumChild()]; 
                Arrays.fill(argSorts, intS);

                // create unique function symbol
                Function constructorFct = new Function(new ProgramElementName(c.getName(), 
                        c.getModule().getName() + "." + c.getDataTypeDecl().getName()), intS, argSorts, null, true);
                initConfig.getServices().getNamespaces().functions().add(constructorFct);
            }
        }

    }

}
