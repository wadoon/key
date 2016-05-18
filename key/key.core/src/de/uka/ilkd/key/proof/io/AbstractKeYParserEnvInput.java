package de.uka.ilkd.key.proof.io;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserConfig;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInitServiceUtil;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.PositionedString;

/**
 * This class can be used to create {@link EnvInput} from data that is either a
 * string of a file on the file system (the subclasses for details).
 * 
 * TODO This class parses the data multiple times (and also reads the data
 * multiple times). A better implementation should extract all parsing
 * information in one go.
 */
public abstract class AbstractKeYParserEnvInput implements EnvInput, ProofOblInput {

    private Term problemTerm = null;
    private String problemHeader = "";
    protected KeYParserF lastParser;

    private final Profile profile;

    private Includes includes;

    protected InitConfig initConfig;

    protected AbstractKeYParserEnvInput(Profile profile) {
        this.profile = profile;
    }

    public AbstractKeYParserEnvInput() {
        this(AbstractProfile.getDefaultProfile());
    }

    @Override
    public Profile getProfile() {
        return profile;
    }

    @Override
    public void setInitConfig(InitConfig conf) {
        this.initConfig = conf;
    }

    @Override
    public Includes readIncludes() throws ProofInputException {
        if (includes == null) {
            KeYParserF problemParser = null;
            try {
                ParserConfig pc = new ParserConfig(new Services(getProfile()), new NamespaceSet());
                // FIXME: there is no exception handler here, thus, when parsing
                // errors are ecountered
                // during collection of includes (it is enough to mispell
                // \include) the error
                // message is very uninformative - ProofInputException without
                // filename, line and column
                // numbers. Somebody please fix that. /Woj
                problemParser = new KeYParserF(ParserMode.PROBLEM, getKeYLexer(), pc, pc, null, null);
                problemParser.parseIncludes();
                includes = problemParser.getIncludes();
            } catch (RecognitionException e) {
                // problemParser cannot be null since exception is thrown during
                // parsing.
                String message = problemParser.getErrorMessage(e);
                throw new ProofInputException(message, e);
            } catch (de.uka.ilkd.key.util.ExceptionHandlerException ehe) {
                throw new ProofInputException(ehe);
            } finally {
                closeLexerStream();
            }
        }
        return includes;
    }
    
    protected final ProofSettings getProofSettings() throws ProofInputException {
        if (initConfig.getSettings() == null) {
            return readPreferences();
        } else {
            return initConfig.getSettings();
        }
    }

    public ProofSettings readPreferences() throws ProofInputException {
        KeYParserF problemParser = null;
        try {
            problemParser = new KeYParserF(ParserMode.PROBLEM, getKeYLexer());
            problemParser.profile();
            ProofSettings settings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
            settings.loadSettingsFromString(problemParser.preferences());
            return settings;
        } catch (RecognitionException e) {
            // problemParser cannot be null since exception is thrown during
            // parsing.
            String message = problemParser.getErrorMessage(e, problemParser.getTokenNames());
            throw new ProofInputException(message, e);
        } catch (de.uka.ilkd.key.util.ExceptionHandlerException ehe) {
            throw new ProofInputException(ehe.getCause().getMessage());
        } finally {
            closeLexerStream();
        }
    }
    
    public void readProblem(KeYLexerF lexer) throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("KeYUserProblemFile: InitConfig not set.");
        }
        
        KeYParserF problemParser = null;
        try {

            final ParserConfig normalConfig 
                = new ParserConfig(initConfig.getServices(), initConfig.namespaces());
            final ParserConfig schemaConfig 
                = new ParserConfig(initConfig.getServices(), initConfig.namespaces());
            
            problemParser = new KeYParserF(ParserMode.PROBLEM,
                                    lexer,
                                    schemaConfig, 
                                    normalConfig,
                                    initConfig.getTaclet2Builder(),
                                    initConfig.getTaclets()); 

            problemTerm = problemParser.parseProblem();

        if(problemTerm == null) {
           boolean chooseDLContract = problemParser.getChooseContract() != null;
          boolean proofObligation = problemParser.getProofObligation() != null;
                if(!chooseDLContract && !proofObligation) {
             throw new ProofInputException(
                     "No \\problem or \\chooseContract or \\proofObligation in the input file!");
           }
        }

            problemHeader = problemParser.getProblemHeader();
            // removed unnecessary check, keep them as assertions. (MU, Nov 14)
            assert problemHeader != null;
            assert problemHeader.lastIndexOf("\\problem") == -1;
            assert problemHeader.lastIndexOf("\\proofObligation") == -1;
            assert problemHeader.lastIndexOf("\\chooseContract") == -1;

            initConfig.setTaclets(problemParser.getTaclets());
            lastParser = problemParser;
        } catch(RecognitionException e) {
            // problemParser cannot be null here
            String message = problemParser.getErrorMessage(e);
            throw new ProofInputException(message, e);
        }
    }

    
    @Override
    public ProofAggregate getPO() throws ProofInputException {
        assert problemTerm != null;
        String name = name();
        ProofSettings settings = getProofSettings();
        initConfig.setSettings(settings);
        return ProofAggregate.createProofAggregate(
                new Proof(name, 
                          problemTerm, 
                          problemHeader,
                          initConfig), 
                name);
    }
    
    @Override
    public boolean implies(ProofOblInput po) {
        return equals(po);
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public KeYJavaType getContainerType() {
       return null;
    }
    
    /** 
     * Reads a saved proof of a .key file.
     */
    public void readProof(IProofFileParser prl) throws ProofInputException {
        if (lastParser == null) {
            readProblem();
        }
        try {
            lastParser.proof(prl);
        } catch (RecognitionException ex) {
            // problemParser cannot be null
            String message = lastParser.getErrorMessage(ex);
            throw new ProofInputException(message, ex);
        } finally {
            lastParser = null;
        }
    }
    
    /**
     * Tries to read the {@link Profile} from the data to load.
     */
    protected Profile readProfileFromData() {
        try {
            KeYParserF problemParser = new KeYParserF(ParserMode.GLOBALDECL, getKeYLexer());
            problemParser.profile();
            String profileName = problemParser.getProfileName();
            if (profileName != null && !profileName.isEmpty()) {
                return ProofInitServiceUtil.getDefaultProfile(profileName);
            } else {
                return profile;
            }
        } catch (RecognitionException e) {
            e.printStackTrace();
            return profile;
        } finally {
            try {
                closeLexerStream();
            } catch (ProofInputException e) {
                // We cannot throw exceptions in this method, so we print the
                // stacktrace instead.
                e.printStackTrace();
            }
        }
    }
    
    protected ImmutableSet<PositionedString> read(KeYLexerF lexer) throws ProofInputException {
        final ParserConfig normalConfig = new ParserConfig(initConfig.getServices(), initConfig.namespaces());
        final ParserConfig schemaConfig = new ParserConfig(initConfig.getServices(), initConfig.namespaces());
        KeYParserF problemParser = new KeYParserF(ParserMode.PROBLEM, lexer, schemaConfig, normalConfig,
                initConfig.getTaclet2Builder(), initConfig.getTaclets());
        try {
            problemParser.problem();
        } catch (RecognitionException e) {
            throw new ProofInputException(problemParser.getErrorMessage(e), e);
        }
        initConfig.addCategory2DefaultChoices(problemParser.getCategory2Default());
        ImmutableSet<Taclet> st = problemParser.getTaclets();
        initConfig.setTaclets(st);

        SpecificationRepository specRepos = initConfig.getServices().getSpecificationRepository();
        specRepos.addContracts(problemParser.getContracts());
        specRepos.addClassInvariants(problemParser.getInvariants());
        chooseContract = problemParser.getChooseContract();
        proofObligation = problemParser.getProofObligation();
        return DefaultImmutableSet.nil();
    }
    
    /**
     * This method can be used to close a stream that has been for for reading
     * data after work with a lexer is done.
     */
    protected abstract void closeLexerStream() throws ProofInputException;
    
    /**
     * Creates a new {@link KeYLexerF}. {{@link #closeLexerStream()}} operation should be
     * executed when the work with the obtained lexer is done.
     */
    protected abstract KeYLexerF getKeYLexer() throws ProofInputException;
    
    private String chooseContract = null;

    private String proofObligation = null;
    
    public String chooseContract() {
        return chooseContract;
    }
    
    
    public String getProofObligation() {
        return proofObligation;
    }

}
