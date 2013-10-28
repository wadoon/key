// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.keyabs.proof.io;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.CountingBufferedReader;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.IKeYFile;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;
import de.uka.ilkd.keyabs.parser.ABSKeYLexer;
import de.uka.ilkd.keyabs.parser.ABSKeYParser;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.proof.init.ABSTacletGenerator;
import de.uka.ilkd.keyabs.proof.mgt.ABSSpecificationRepository;
import de.uka.ilkd.keyabs.speclang.dl.ABSClassInvariant;
import de.uka.ilkd.keyabs.speclang.dl.InterfaceInvariant;


/** 
 * Represents an input from a .key file producing an environment.
 */
public class ABSKeYFile implements IKeYFile<ABSServices, ABSInitConfig> {
    
    private final String name;
    
    /** the RuleSource delivering the input stream for the file.
     */
    protected final RuleSource file;
   
    /** the graphical entity to notify on the state of reading.
     */
    protected final ProgressMonitor monitor;
    
    private String javaPath;
    private boolean javaPathAlreadyParsed=false;
    
    private InputStream input;
    
    protected ABSInitConfig initConfig;
    
    private String chooseContract = null;

    // when parsing the key file store the classPaths here
    private ImmutableList<String> classPaths;
    
    // when parsing the key file store the boot class path here (or null if none given)
    private String bootClassPath;

    // main module
    private String mainModule;

    // main class
    private String mainClass;


    private Includes includes;

	private String proofObligation;
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    /** creates a new representation for a given file by indicating a name
     * and a RuleSource representing the physical source of the .key file.
     */
    public ABSKeYFile(String name, 
                   RuleSource file, 
                   ProgressMonitor monitor) {
        assert name != null;
        assert file != null;
        this.name = name;
        this.file = file;
        this.monitor = monitor;
    }

        
    /** creates a new representation for a given file by indicating a name
     * and a file representing the physical source of the .key file.
     */
    public ABSKeYFile(String name, 
                   File file, 
                   ProgressMonitor monitor) {
	    this(name, RuleSource.initRuleFile(file), monitor);
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private ABSKeYParser createDeclParser(InputStream is) throws FileNotFoundException {
        return new ABSKeYParser(ParserMode.DECLARATION,
                             new ABSKeYLexer(is,
                                          initConfig.getServices().getExceptionHandler()),
                             file.toString(), 
                             initConfig.getServices(),
                             initConfig.namespaces());
    }


    protected InputStream getNewStream() throws FileNotFoundException {
        close();
        if (!file.isAvailable()) {
            throw new FileNotFoundException("File/Resource " + file + " not found.");  
        } 
        input = file.getNewStream();
        return input;
    }
    
    
    protected ProofSettings getPreferences() throws ProofInputException {
        if (initConfig.getSettings() == null) {
            if (file.isDirectory()) {
                return null;
            }
            try {
                ABSKeYParser problemParser 
                    = new ABSKeYParser(ParserMode.PROBLEM,
                                    new ABSKeYLexer(getNewStream(), null), 
                                    file.toString());
                ProofSettings settings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
                settings.setProfile(ProofSettings.DEFAULT_SETTINGS.getProfile());
                settings.loadSettingsFromString(problemParser.preferences());
                initConfig.setSettings(settings);
                return settings;                
            } catch (antlr.ANTLRException e) {
                throw new ProofInputException(e);
            } catch (FileNotFoundException fnfe) {
                throw new ProofInputException(fnfe);
            } catch (de.uka.ilkd.key.util.ExceptionHandlerException ehe) {
                throw new ProofInputException(ehe.getCause().getMessage());
            }
        } else {
            return initConfig.getSettings();
        }
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    @Override
    public String name() {
        return name;
    }

    public String getMainModule() {
        return mainModule;
    }

    public String getMainClassName() {
        return mainClass;
    }
    
    @Override
    public int getNumberOfChars() {
	return file.getNumberOfChars();
    }
    
    
    @Override
    public void setInitConfig(ABSInitConfig conf) {
        this.initConfig = conf;
    }

    
    @Override
    public Includes readIncludes() throws ProofInputException {
        if (includes == null) {
            try {
                ParserConfig<ABSServices> pc = new ParserConfig<ABSServices>(new ABSServices(), 
                        new NamespaceSet());
                // FIXME: there is no exception handler here, thus, when parsing errors are ecountered
                // during collection of includes (it is enough to mispell \include) the error
                // message is very uninformative - ProofInputException without filename, line and column
                // numbers. Somebody please fix that. /Woj
                ABSKeYParser problemParser = new ABSKeYParser(ParserMode.PROBLEM, 
                        new ABSKeYLexer(getNewStream(),
                                null), 
                                file.toString(), 
                                pc, 
                                pc, 
                                null, 
                                null); 
                problemParser.parseIncludes(); 
                includes = problemParser.getIncludes();
            } catch (antlr.ANTLRException e) {
                throw new ProofInputException(e);
            } catch (FileNotFoundException fnfe) {
                throw new ProofInputException(fnfe);
            } catch(de.uka.ilkd.key.util.ExceptionHandlerException ehe){
                throw new ProofInputException(ehe);
            }
        }
        return includes;            
    }


    @Override    
    public File readBootClassPath() {
        if(!javaPathAlreadyParsed) {
            throw new IllegalStateException("Can access this only after 'readJavaPath' has been called");
        }
        
        if(bootClassPath == null) {
            return null;
        }
        
        String parentDirectory = file.file().getParent();
        return new File(parentDirectory, bootClassPath);
    }
    

    @Override    
    public List<File> readClassPath() {
        if(!javaPathAlreadyParsed) {
            throw new IllegalStateException("Can access this only after 'readJavaPath' has been called");
        }

        String parentDirectory = file.file().getParent();
        List<File> fileList = new ArrayList<File>();
        for (String cp : classPaths) {
            if (cp == null) {
                fileList.add(null);
            } else {
                File f = new File(cp);
                if (!f.isAbsolute()) {
                    f = new File(parentDirectory, cp);
                }
                fileList.add(f);
            }
        }
        return fileList;
    }

    
    @Override    
    public String readJavaPath() throws ProofInputException {
        if (javaPathAlreadyParsed) {
            return javaPath;       
        }
        try {
            ABSKeYParser problemParser = new ABSKeYParser(ParserMode.PROBLEM,
                                                    new ABSKeYLexer(getNewStream(),
                                                                 null), 
                                                    file.toString());
            
            problemParser.preferences(); // skip preferences

            bootClassPath = problemParser.bootClassPath();
            classPaths = problemParser.classPaths();
            javaPath = problemParser.javaSource();

            mainModule = problemParser.mainModule();
            mainClass  = mainModule + "." + problemParser.mainClass();

            if(javaPath != null) {
                File cfile = new File(javaPath);
                if (!cfile.isAbsolute()) { // test relative pathname
                    File parent=file.file().getParentFile();
                    cfile = new File(parent,javaPath).
                    getCanonicalFile().getAbsoluteFile();
                    javaPath = cfile.getAbsolutePath();
                }
                if (!cfile.exists()) {
                    throw new ProofInputException("Declared Java source " 
                            + javaPath + " not found.");
                }                      
            }
            
            javaPathAlreadyParsed = true;
            
            return javaPath;
        } catch (antlr.ANTLRException e) {
            throw new ProofInputException(e);
        } catch (IOException ioe) {
            throw new ProofInputException(ioe);
        } catch(de.uka.ilkd.key.util.ExceptionHandlerException ehe){
            ehe.printStackTrace();
            System.out.println(ehe.getCause().getMessage());
            throw new ProofInputException(ehe.getCause().getMessage());
        }
    }
    
    
    @Override
    public void read() throws ProofInputException {
	if(initConfig == null) {
	    throw new IllegalStateException("ABSKeYFile: InitConfig not set.");
	}
        
        //read .key file
	try {
            Debug.out("Reading ABSKeY file", file);
                   
            final ParserConfig<ABSServices> normalConfig 
                    = new ParserConfig<ABSServices>(initConfig.getServices(), initConfig.namespaces());                       
            final ParserConfig<ABSServices> schemaConfig 
                    = new ParserConfig<ABSServices>(initConfig.getServices(), initConfig.namespaces());

            CountingBufferedReader cinp = 
                    new CountingBufferedReader
                        (getNewStream(),monitor,getNumberOfChars()/100);
            try {
                ABSKeYParser problemParser 
                = new ABSKeYParser(ParserMode.PROBLEM, 
                        new ABSKeYLexer(cinp, 
                                initConfig.getServices()
                                .getExceptionHandler()), 
                                file.toString(), 
                                schemaConfig, 
                                normalConfig, 
                                initConfig.getTaclet2Builder(), 
                                initConfig.getTaclets()); 
                problemParser.problem(); 
                initConfig.addCategory2DefaultChoices(problemParser.
                        getCategory2Default());
                ImmutableSet<Taclet> st = problemParser.getTaclets();

                initConfig.setTaclets(st);

                ABSSpecificationRepository specRepos
                = initConfig.getServices().getSpecificationRepository();
                specRepos.addInterfaceInvariants(problemParser.getInterfaceInvariants());
                specRepos.addClassInvariants(problemParser.getClassInvariants());
                //specRepos.addContracts(problemParser.getContracts());
                //specRepos.addClassInvariants(problemParser.getInvariants());
                chooseContract = problemParser.getChooseContract();
                Debug.out("Read ABSKeY file   ", file);
            } finally {
                cinp.close();
            }
	} catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
	} catch (FileNotFoundException fnfe) {
	    throw new ProofInputException(fnfe);
        } catch (IOException io) {
            throw new ProofInputException(io);            
        }
    }

    
    /** reads the sorts declaration of the .key file only, 
     * modifying the sort namespace
     * of the initial configuration 
     */
    public void readSorts() throws ProofInputException {
        try {
            InputStream is = getNewStream();
            ABSKeYParser p=createDeclParser(is);          
            p.parseSorts();
            initConfig.addCategory2DefaultChoices(p.getCategory2Default());
	} catch (antlr.ANTLRException e) {
            e.printStackTrace();
	    throw new ProofInputException(e);
	} catch (FileNotFoundException fnfe) {
            fnfe.printStackTrace();
            throw new ProofInputException(fnfe);
        }
    }
    
    
    /** reads the functions and predicates declared in the .key file only, 
     * modifying the function namespaces of the respective taclet options. 
     */
    public void readFuncAndPred() throws ProofInputException {	
	if(file == null) return;
	try {
            InputStream is = getNewStream();
            try { 
                ABSKeYParser p=createDeclParser(getNewStream());
                p.parseFuncAndPred();
            } finally {
                is.close();
            }
	} catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
	} catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        } catch (IOException io) {
            throw new ProofInputException(io);            
        }
    }

    
   /** reads the rules and problems declared in the .key file only, 
     * modifying the set of rules 
     * of the initial configuration 
     */
    public void readRulesAndProblem() 
            throws ProofInputException {
        final ParserConfig<ABSServices> schemaConfig = 
	    new ParserConfig<ABSServices>(initConfig.getServices(), initConfig.namespaces());
        final ParserConfig<ABSServices> normalConfig = 
	    new ParserConfig<ABSServices>(initConfig.getServices(), initConfig.namespaces());
        
        try {
            final CountingBufferedReader cinp = new CountingBufferedReader
                    (getNewStream(), monitor, getNumberOfChars()/100);
            try {
                ABSKeYParser problemParser 
                = new ABSKeYParser(ParserMode.PROBLEM,
                        new ABSKeYLexer(cinp, 
                                initConfig.getServices()
                                .getExceptionHandler()), 
                                file.toString(),
                                schemaConfig,
                                normalConfig,
                                initConfig.getTaclet2Builder(),
                                initConfig.getTaclets());                             
                problemParser.parseTacletsAndProblem();
                initConfig.setTaclets(problemParser.getTaclets());
            } finally {
                cinp.close();
            }
	} catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
	} catch (FileNotFoundException fnfe) {
            throw new ProofInputException(fnfe);
        } catch (IOException io) {
            throw new ProofInputException(io);            
        }
    }

    
    public void close() {
        try {
            if (input != null) { 
		input.close();
	    }
        } catch(IOException ioe) {
            System.err.println("WARNING: Cannot close stream "+file+"\n"+ioe);
        }
    }
    
    
    public String chooseContract() {
        return chooseContract;
    }

    
    @Override    
    public String toString() {
	return name() + " " + file.toString();
    }
    
    
    @Override    
    public boolean equals(Object o) {
        if(!(o instanceof ABSKeYFile)) {
            return false;
        }
        ABSKeYFile kf = (ABSKeYFile) o;
        return kf.file.getExternalForm().equals(file.getExternalForm());

    }

    
    @Override    
    public int hashCode(){
        final String externalForm = file.getExternalForm();
        if (externalForm == null) {
            return -1;
        }
	return externalForm.hashCode();
    }


    @Override
    public ABSInitConfig getInitConfig() {
        return initConfig;
    }

    public ImmutableSet<Taclet> collectInterfaceInvariantTaclets(ABSServices services) {
        ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();
        ABSSpecificationRepository repository = services.getSpecificationRepository();

        for (KeYJavaType type : services.getProgramInfo().getAllKeYJavaTypes()) {
            ImmutableSet<InterfaceInvariant> invs = repository.getInterfaceInvariants(type);
            if (!invs.isEmpty() && type.getJavaType() instanceof ABSInterfaceType) {
                ABSTacletGenerator tg = new ABSTacletGenerator();
                result = result.add(tg.generateTacletForInterfaceInvariant(type, invs, services));
            }
        }
        return result;
    }

    public ImmutableSet<Taclet> getClassInvariantTaclet(ABSServices services) {
        ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();

        ABSSpecificationRepository repository = services.getSpecificationRepository();
        ImmutableSet<ABSClassInvariant> cinvs = repository.getClassInvariants(getMainClassName());

        if (!cinvs.isEmpty()) {
            ABSTacletGenerator tg = new ABSTacletGenerator();
            result = result.add(tg.generateTacletForClassInvariant(getMainClassName(),
                    cinvs, services));
        }
        return result;
    }


	public String getProofObligation() {
        return proofObligation;
	}


}
