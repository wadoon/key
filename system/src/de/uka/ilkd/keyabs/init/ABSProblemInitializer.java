package de.uka.ilkd.keyabs.init;

import java.util.Arrays;

import abs.frontend.ast.DataConstructor;
import abs.frontend.ast.List;
import de.uka.ilkd.key.java.IServices;
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
import de.uka.ilkd.keyabs.abs.converter.ABSInterfaceCollector;
import de.uka.ilkd.keyabs.init.io.ABSKeYFile;

public class ABSProblemInitializer extends AbstractProblemInitializer {

    public ABSProblemInitializer(ProgressMonitor mon, Profile profile,
            IServices services, boolean registerProof,
            ProblemInitializerListener listener) {
        super(mon, profile, services, registerProof, listener);
    }
    
    public ABSProblemInitializer(ProgressMonitor mon,
            Profile profile, 
            boolean registerProof,
            ProblemInitializerListener listener) {
        this(mon, profile, 
                profile.createServices(new KeYRecoderExcHandler()), 
                registerProof, listener);
    }


    @Override
    protected void registerProgramDefinedSymbols(AbstractInitConfig initConfig)
            throws ProofInputException {
    }

    @Override
    protected void readJava(EnvInput envInput, AbstractInitConfig initConfig)
            throws ProofInputException {
    
        
        ABSInterfaceCollector collector = new ABSInterfaceCollector();
        
        collector.collect();
        
        for (List<DataConstructor>  constructors  : collector.getDataTypes2dataConstructors().values()) {
            for (DataConstructor c : constructors) {
                System.out.println("" + c.getName() + ":" + c.getConstructorArgs());
                
                Sort intS = initConfig.getServices().getTypeConverter().getIntegerLDT().targetSort();
                
                Sort[] argSorts = new Sort[c.getConstructorArgList().getNumChild()]; 
                Arrays.fill(argSorts, intS);
                
                // create unique function symbol
                Function constructorFct = new Function(new ProgramElementName(c.getName(), 
                        c.getModule().getName() + "." + c.getDataTypeDecl().getName()), intS, argSorts, null, true);
                
                System.out.println(constructorFct + ":" + constructorFct.arity());
                
                initConfig.getServices().getNamespaces().functions().add(constructorFct);
            }
        }
        
        initConfig.getProofEnv().setJavaModel(JavaModel.NO_MODEL);

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

}
