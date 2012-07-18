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

import java.io.File;
import java.util.List;
import java.util.Vector;

import recoder.io.PathList;
import recoder.io.ProjectSettings;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.key.util.ProgressMonitor;


public final class ProblemInitializer extends AbstractProblemInitializer {

    
    public ProblemInitializer(ProgressMonitor mon,
	                      Profile profile, IServices services, boolean registerProof,
	                      ProblemInitializerListener listener) {
	super(mon, profile, services, registerProof, listener);
    }

    public ProblemInitializer(ProgressMonitor mon,
            Profile profile, 
            boolean registerProof,
            ProblemInitializerListener listener) {
        this(mon, profile, 
                profile.createServices(new KeYRecoderExcHandler()), 
                registerProof, listener);
    }

    
    public ProblemInitializer(Profile profile) {
	this(null, profile, false, null);
    }
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    /**
     * get a vector of Strings containing all .java file names 
     * in the cfile directory.
     * Helper for readJava().
     */
    private Vector<String> getClasses(String f) throws ProofInputException  {
	File cfile = new File(f);
	Vector<String> v=new Vector<String>();
	if(cfile.isDirectory()) {
	    String[] list=cfile.list();
	    // mu(2008-jan-28): if the directory is not readable for the current user
	    // list is set to null, which results in a NullPointerException.
	    if(list != null) {
	        for (int i=0; i<list.length; i++) {
	            String fullName = cfile.getPath()+File.separator+list[i];
	            File n=new File(fullName);
	            if (n.isDirectory()) {		    
	                v.addAll(getClasses(fullName));
	            } else if (list[i].endsWith(".java")) {
	                v.add(fullName);	
	            }
	        }
	    }
	    return v;
	} else {
	   throw new ProofInputException("Java model path "+f+" not found.");
	}
	
    }
    
    
    /**
     * Helper for readJava().
     */
    private static JavaModel createJavaModel(String javaPath,
	    			      List<File> classPath,
	    			      File bootClassPath) 
    		throws ProofInputException {
	JavaModel result;
	if(javaPath == null) {
	    result = JavaModel.NO_MODEL;
	} else if (javaPath.equals(System.getProperty("user.home"))) { 
	    throw new ProofInputException("You do not want to have "+
	    "your home directory as the program model.");
	} else { 
	    String modelTag = "KeY_" + new Long((new java.util.Date()).getTime());
	    result = new JavaModel(javaPath, 
		    		   modelTag,
		    		   classPath,
		    		   bootClassPath);
	}
	return result;
    }
         
    
    /**
     * Helper for readEnvInput().
     */
    @Override
    protected void readJava(EnvInput envInput, AbstractInitConfig initConfig) 
    		throws ProofInputException {
	//this method must only be called once per init config	
        final Services javaServices = (Services) initConfig.getServices();
        assert !javaServices
        .getJavaInfo()
        .rec2key()
        .parsedSpecial();
        assert initConfig.getProofEnv().getJavaModel() == null;

	//read Java source and classpath settings
	envInput.setInitConfig(initConfig);
	final String javaPath = envInput.readJavaPath();
	final List<File> classPath = envInput.readClassPath();
	final File bootClassPath = envInput.readBootClassPath();
	
	//create Recoder2KeY, set classpath
	final Recoder2KeY r2k = new Recoder2KeY((Services) javaServices, 
                                                initConfig.namespaces());
	r2k.setClassPath(bootClassPath, classPath);

    	//read Java (at least the library classes)		
	if(javaPath != null) {
            reportStatus("Reading Java source");
            final ProjectSettings settings 
            	=  javaServices
            	             .getJavaInfo()
            	             .getKeYProgModelInfo()
                	     .getServConf()
                	     .getProjectSettings();
            final PathList searchPathList = settings.getSearchPathList();
            if(searchPathList.find(javaPath) == null) {
                searchPathList.add(javaPath);
            }
            final String[] cus = getClasses(javaPath).toArray(new String[]{});
            r2k.readCompilationUnitsAsFiles(cus);
	} else {
            reportStatus("Reading Java libraries");	    
	    r2k.parseSpecialClasses();
	}
        initConfig.getProofEnv().setJavaModel(createJavaModel(javaPath,
        	                                              classPath,
        	                                              bootClassPath));
    }
    
    
    
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 
    
    @Override
    protected void registerProgramDefinedSymbols(AbstractInitConfig initConfig)
            throws ProofInputException {
        final JavaInfo javaInfo = (JavaInfo) initConfig.getServices().getProgramInfo();
        final Namespace functions 
        = initConfig.getServices().getNamespaces().functions();
        final HeapLDT heapLDT 
        = initConfig.getServices().getTypeConverter().getHeapLDT();
        assert heapLDT != null;
        if (javaInfo != null) {
            functions.add(javaInfo.getInv());
            for(KeYJavaType kjt : javaInfo.getAllKeYJavaTypes()) {
                final Type type = kjt.getJavaType();
                if(type instanceof ClassDeclaration 
                        || type instanceof InterfaceDeclaration) {
                    for(Field f : javaInfo.getAllFields((TypeDeclaration)type)) {
                        final ProgramVariable pv 
                        = (ProgramVariable)f.getProgramVariable();
                        if(pv instanceof LocationVariable) {
                            heapLDT.getFieldSymbolForPV((LocationVariable)pv, 
                                    initConfig.getServices());
                        }
                    }
                }
                for(IProgramMethod pm
                        : javaInfo.getAllProgramMethodsLocallyDeclared(kjt)) {
                    if(!(pm.isVoid() || pm.isConstructor())) {
                        functions.add(pm);
                    }
                }
            }
        } else
                throw new ProofInputException("Problem initialization without JavaInfo!");
    }

}
