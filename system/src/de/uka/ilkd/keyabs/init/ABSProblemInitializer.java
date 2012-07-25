package de.uka.ilkd.keyabs.init;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import abs.frontend.ast.ConstructorArg;
import abs.frontend.ast.DataConstructor;
import abs.frontend.ast.DataTypeDecl;
import abs.frontend.ast.DataTypeUse;
import abs.frontend.ast.ParametricDataTypeDecl;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
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
import de.uka.ilkd.keyabs.logic.ldt.HistoryLDT;

public class ABSProblemInitializer extends AbstractProblemInitializer<ABSServices> {

    public ABSProblemInitializer(ProgressMonitor mon, Profile profile,
            boolean registerProof, ProblemInitializerListener listener) {
        this(mon, profile, (ABSServices) profile.createServices(new KeYRecoderExcHandler()),
                registerProof, listener);
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
    protected void readJava(EnvInput envInput, AbstractInitConfig initConfig)
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

        parserInfo.finish(initConfig.getServices());

        initConfig.getProofEnv().setJavaModel(absModelDescription);
    }

    @Override
    protected void registerProgramDefinedSymbols(AbstractInitConfig initConfig)
            throws ProofInputException {

        ABSInfo info = (ABSInfo) initConfig.getServices().getProgramInfo();

        System.out.println("Registering Sorts (" + info.getAllKeYJavaTypes().size() + ")");
        // register sorts

        for (KeYJavaType t : info.getAllKeYJavaTypes()) {
            if (initConfig.sortNS().lookup(t.getSort().name()) == null) {
                initConfig.sortNS().addSafely(t.getSort());
            } else {
                System.out
                        .println(getClass() + ": Skipping " + t.getFullName());
            }
        }

        System.out.println("Instantiating Generic Datatypes");
        for ( DataTypeDecl d : info.getABSParserInfo().getParametricDatatypes().getDatatypes().values()) {
        	if (((ParametricDataTypeDecl)d).getNumTypeParameter() > 1) {
        		System.out.println("Skipping data types with more than one parameter");
        		continue;
        	}
        	//to do: KeYJavaType
        	
        	
        }


        System.out.println("Register future types");
        
        HistoryLDT historyLDT = services.getTypeConverter().getHistoryLDT();
        
        GenericSort depSort = new GenericSort(new Name("T"));
		SortDependingFunction futGetterProto = SortDependingFunction.createFirstInstance(depSort, 
        		new Name("get"), depSort, new Sort[]{historyLDT.targetSort()}, false);

		for (KeYJavaType t : info.getAllKeYJavaTypes()) {
        	SortImpl fut = new SortImpl(new Name("ABS.StdLib.Fut<" + t.getFullName() + ">"), 
        			historyLDT.getFutureSort());
			initConfig.sortNS().addSafely(fut);
			futGetterProto.getInstanceFor(t.getSort(), initConfig.getServices());
        
		//TODO at KeYJavaType
		}
        
        System.out.println("Registering Constructors");

        // test code
        for (List<DataConstructor> constructors : info.getABSParserInfo()
                .getDatatypes().getDataTypes2dataConstructors().values()) {
            for (DataConstructor c : constructors) {
                Sort[] argSorts = new Sort[c.getConstructorArgList()
                        .getNumChild()];

                try {
                    int count = 0;
                    for (ConstructorArg arg : c.getConstructorArgs()) {
                        argSorts[count++] = initConfig
                                .getServices()
                                .getProgramInfo()
                                .getTypeByName(arg.getType().getQualifiedName())
                                .getSort();
                    }
                    if (count == argSorts.length) {
                        // create unique function symbol
                        final String fullyQualifiedName = c.getModule()
                                .getName()
                                + "."
                                + c.getDataTypeDecl().getName();
                        Sort returnSort = initConfig.getServices()
                                .getProgramInfo()
                                .getTypeByName(c.getType().getQualifiedName())
                                .getSort();
                        Function constructorFct = new Function(
                                new ProgramElementName(c.getName(),
                                        fullyQualifiedName), returnSort,
                                argSorts, null, true);
                        initConfig.getServices().getNamespaces().functions()
                                .add(constructorFct);
                    }

                } catch (Exception e) {
                    e.printStackTrace();
                }
            }
        }
        
        System.out.println("Register Interface Label Constants");

        for (Name itf : info.getABSParserInfo().getInterfaces().keySet()) {
                Function interfaceLabel = 
                        new Function(itf, services.getTypeConverter().getHistoryLDT().getInterfaceLabelSort(),
                                new Sort[0], null, true);
                initConfig.getServices().getNamespaces().functions().add(interfaceLabel);
                    
        }

        System.out.println("Register Interface Class Constants");
        
        for (Name itf : info.getABSParserInfo().getClasses().keySet()) {
			Function classLabel = 
                    new Function(itf, historyLDT.getClassLabelSort(),
                            new Sort[0], null, true);
            initConfig.getServices().getNamespaces().functions().add(classLabel);
                
        }
        
        System.out.println("Register method label");
    
    }

}
