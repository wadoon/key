package de.uka.ilkd.key.proof.io;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.zip.ZipFile;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.io.consistency.DiskFileRepo;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.io.consistency.SimpleFileRepo;
import de.uka.ilkd.key.prover.impl.PerfScope;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

import org.key_project.util.java.IOUtil;
import org.key_project.util.reflection.ClassLoaderUtil;

import org.antlr.runtime.MismatchedTokenException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * <p>
 * This class provides the basic functionality to load something in KeY. The loading process is done
 * in the current {@link Thread} and no user interaction is required.
 * </p>
 * <p>
 * The basic usage of this class is to instantiate a new {@link SingleThreadProblemLoader} or
 * {@link ProblemLoader} instance which should load the file configured by the constructor's
 * arguments. The next step is to call {@link #load()} which does the loading process and tries to
 * instantiate a proof and to apply rules again if possible. The result of the loading process is
 * available via the getter methods.
 * </p>
 *
 * @author Martin Hentschel
 */
public abstract class AbstractProblemLoader {
    private static final Logger LOGGER = LoggerFactory.getLogger(AbstractProblemLoader.class);

    /**
     * If set to true, only the given Java file will be parsed and loaded.
     *
     * @see EnvInput#isIgnoreOtherJavaFiles()
     */
    private boolean loadSingleJavaFile = false;

    public static class ReplayResult {

        private final Node node;
        private final List<Throwable> errors;
        private final String status;

        public ReplayResult(String status, List<Throwable> errors, Node node) {
            this.status = status;
            this.errors = errors;
            this.node = node;
        }

        public Node getNode() {
            return node;
        }

        public String getStatus() {
            return status;
        }

        public List<Throwable> getErrorList() {
            return errors;
        }

        public boolean hasErrors() {
            return errors != null && !errors.isEmpty();
        }

    }

    /**
     * The file or folder to load.
     */
    private final File file;

    /**
     * The filename of the proof in the zipped file (null if file is not a proof bundle).
     */
    private File proofFilename;

    /**
     * The optional class path entries to use.
     */
    private final List<File> classPath;

    /**
     * An optional boot class path.
     */
    private final File bootClassPath;

    /**
     * The global includes to use.
     */
    private final List<File> includes;

    /**
     * The {@link ProblemLoaderControl} to use.
     */
    private final ProblemLoaderControl control;

    /**
     * The {@link Profile} to use for new {@link Proof}s.
     */
    private final Profile profileOfNewProofs;

    /**
     * {@code true} to call {@link UserInterfaceControl#selectProofObligation(InitConfig)} if no
     * {@link Proof} is defined by the loaded proof or {@code false} otherwise which still allows to
     * work with the loaded {@link InitConfig}.
     */
    private final boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile;

    /**
     * Some optional additional {@link Properties} for the PO.
     */
    private final Properties poPropertiesToForce;

    /**
     * {@code} true {@link #profileOfNewProofs} will be used as {@link Profile} of new proofs,
     * {@code false} {@link Profile} specified by problem file will be used for new proofs.
     */
    private final boolean forceNewProfileOfNewProofs;

    /**
     * The instantiated {@link EnvInput} which describes the file to load.
     */
    private EnvInput envInput;

    /**
     * The instantiated {@link ProblemInitializer} used during the loading process.
     */
    private ProblemInitializer problemInitializer;

    /**
     * The instantiated {@link InitConfig} which provides access to the loaded source elements and
     * specifications.
     */
    private InitConfig initConfig;

    /**
     * The instantiate proof or {@code null} if no proof was instantiated during loading process.
     */
    private Proof proof;

    /**
     * The {@link ReplayResult} if available or {@code null} otherwise.
     */
    private ReplayResult result;

    /**
     * Whether warnings (generated when loading the proof) should be ignored
     * and not shown to the user.
     */
    private boolean ignoreWarnings = false;

    /**
     * Maps internal error codes of the parser to human readable strings. The integers refer to the
     * common MismatchedTokenExceptions, where one token is expected and another is found. Both are
     * usually only referred to by their internal code.
     */
    private final static Map<Pair<Integer, Integer>, String> mismatchErrors;
    private final static Map<Integer, String> missedErrors;

    static {
        // format: (expected, found)
        mismatchErrors = new HashMap<>();
        mismatchErrors.put(new Pair<>(KeYLexer.SEMI, KeYLexer.COMMA),
            "there may be only one declaration per line");

        missedErrors = new HashMap<>();
        missedErrors.put(KeYLexer.RPAREN, "closing parenthesis");
        missedErrors.put(KeYLexer.RBRACE, "closing brace");
        missedErrors.put(KeYLexer.SEMI, "semicolon");
    }

    /**
     * Constructor.
     *
     * @param file The file or folder to load.
     * @param classPath The optional class path entries to use.
     * @param bootClassPath An optional boot class path.
     * @param includes Optional includes to consider.
     * @param profileOfNewProofs The {@link Profile} to use for new {@link Proof}s.
     * @param forceNewProfileOfNewProofs {@code} true {@link #profileOfNewProofs} will be used as
     *        {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file
     *        will be used for new proofs.
     * @param control The {@link ProblemLoaderControl} to use.
     * @param askUiToSelectAProofObligationIfNotDefinedByLoadedFile {@code true} to call
     *        {@link UserInterfaceControl#selectProofObligation(InitConfig)} if no {@link Proof} is
     *        defined by the loaded proof or {@code false} otherwise which still allows to work with
     *        the loaded {@link InitConfig}.
     */
    public AbstractProblemLoader(File file, List<File> classPath, File bootClassPath,
            List<File> includes, Profile profileOfNewProofs, boolean forceNewProfileOfNewProofs,
            ProblemLoaderControl control,
            boolean askUiToSelectAProofObligationIfNotDefinedByLoadedFile,
            Properties poPropertiesToForce) {
        this.file = file;
        this.classPath = classPath;
        this.bootClassPath = bootClassPath;
        this.control = control;
        this.profileOfNewProofs =
            profileOfNewProofs != null ? profileOfNewProofs : AbstractProfile.getDefaultProfile();
        this.forceNewProfileOfNewProofs = forceNewProfileOfNewProofs;
        this.askUiToSelectAProofObligationIfNotDefinedByLoadedFile =
            askUiToSelectAProofObligationIfNotDefinedByLoadedFile;
        this.poPropertiesToForce = poPropertiesToForce;
        this.includes = includes;
    }

    protected void setProof(Proof proof) {
        this.proof = proof;
    }

    /**
     * Executes the loading process and tries to instantiate a proof and to re-apply rules on it if
     * possible.
     *
     * @throws ProofInputException Occurred Exception.
     * @throws IOException Occurred Exception.
     * @throws ProblemLoaderException Occurred Exception.
     */
    public final void load() throws ProofInputException, IOException, ProblemLoaderException {
        load(null);
    }

    /**
     * Executes the loading process and tries to instantiate a proof and to re-apply rules on it if
     * possible.
     *
     * @param callbackProofLoaded optional callback, called when the proof is loaded but not yet
     *        replayed
     *
     * @throws ProofInputException Occurred Exception.
     * @throws IOException Occurred Exception.
     * @throws ProblemLoaderException Occurred Exception.
     */
    public final void load(Consumer<Proof> callbackProofLoaded)
            throws ProofInputException, IOException, ProblemLoaderException {
        control.loadingStarted(this);

        loadEnvironment();


        LoadedPOContainer poContainer = createProofObligationContainer();
        ProofAggregate proofList = null;
        try {
            if (poContainer == null) {
                if (askUiToSelectAProofObligationIfNotDefinedByLoadedFile) {
                    selectAndLoadProof(control, initConfig);
                }
            } else {
                proofList = createProof(poContainer);
                loadSelectedProof(poContainer, proofList, callbackProofLoaded);
            }
        } catch (Throwable t) {
            // Throw this exception; otherwise, it can for instance occur
            // that "result" will be null (if replayProof(...) fails) and
            // we get a NullPointerException that is hard to analyze.
            throw t;
        } finally {
            control.loadingFinished(this, poContainer, proofList, result);
        }
    }

    /**
     * Loads and initialized the proof environment.
     *
     * @throws ProofInputException Occurred Exception.
     * @throws IOException Occurred Exception.
     * @see AbstractProblemLoader#load()
     */
    protected void loadEnvironment() throws ProofInputException, IOException {
        FileRepo fileRepo = createFileRepo();

        var timeBeforeEnv = System.nanoTime();
        LOGGER.info("Loading environment from " + file);
        envInput = createEnvInput(fileRepo);
        LOGGER.debug(
            "Environment load took " + PerfScope.formatTime(System.nanoTime() - timeBeforeEnv));
        problemInitializer = createProblemInitializer(fileRepo);
        var beforeInitConfig = System.nanoTime();
        LOGGER.info("Creating init config");
        initConfig = createInitConfig();
        initConfig.setFileRepo(fileRepo);
        LOGGER.debug(
            "Init config took " + PerfScope.formatTime(System.nanoTime() - beforeInitConfig));
        if (!problemInitializer.getWarnings().isEmpty() && !ignoreWarnings) {
            control.reportWarnings(problemInitializer.getWarnings());
        }
    }

    /**
     * Asks the user to select a proof obligation and loads it.
     *
     * @param control the ui controller.
     * @param initConfig the proof configuration.
     * @see AbstractProblemLoader#load()
     */
    protected void selectAndLoadProof(ProblemLoaderControl control, InitConfig initConfig) {
        control.selectProofObligation(initConfig);
    }

    /**
     * Loads a proof from the proof list.
     *
     * @param poContainer the container created by {@link #createProofObligationContainer()}.
     * @param proofList the proof list containing the proof to load.
     * @param callbackProofLoaded optional callback, called before the proof is replayed
     * @throws ProofInputException Occurred Exception.
     * @throws ProblemLoaderException Occurred Exception.
     * @see AbstractProblemLoader#load()
     */
    protected void loadSelectedProof(LoadedPOContainer poContainer, ProofAggregate proofList,
            Consumer<Proof> callbackProofLoaded)
            throws ProofInputException, ProblemLoaderException {
        // try to replay first proof
        proof = proofList.getProof(poContainer.getProofNum());


        if (proof != null) {
            if (callbackProofLoaded != null) {
                callbackProofLoaded.accept(proof);
            }
            OneStepSimplifier.refreshOSS(proof);
            result = replayProof(proof);
        }
    }

    /**
     * Find first 'non-wrapper' exception type in cause chain.
     */
    private Throwable unwrap(Throwable e) {
        while (e instanceof ExceptionHandlerException || e instanceof ProblemLoaderException) {
            e = e.getCause();
        }
        return e;
    }

    /**
     * Tries to recover parser errors and make them human-readable, rewrap them into
     * ProblemLoaderExceptions.
     */
    protected ProblemLoaderException recoverParserErrorMessage(Exception e) {
        // try to resolve error message
        final Throwable c0 = unwrap(e);
        if (c0 instanceof org.antlr.runtime.RecognitionException) {
            final org.antlr.runtime.RecognitionException re =
                (org.antlr.runtime.RecognitionException) c0;
            final org.antlr.runtime.Token occurrence = re.token; // may be null
            if (c0 instanceof org.antlr.runtime.MismatchedTokenException) {
                if (c0 instanceof org.antlr.runtime.MissingTokenException) {
                    final org.antlr.runtime.MissingTokenException mte =
                        (org.antlr.runtime.MissingTokenException) c0;
                    // TODO: other commonly missed tokens
                    final String readable = missedErrors.get(mte.expecting);
                    final String token = readable == null ? "token id " + mte.expecting : readable;
                    final String msg = "Syntax error: missing " + token
                        + (occurrence == null ? "" : " at " + occurrence.getText()) + " statement ("
                        + mte.input.getSourceName() + ":" + mte.line + ")";
                    return new ProblemLoaderException(this, msg, mte);
                    // TODO other ANTLR exceptions
                } else {
                    final org.antlr.runtime.MismatchedTokenException mte =
                        (MismatchedTokenException) c0;
                    final String genericMsg = "expected " + mte.expecting + ", but found " + mte.c;
                    final String readable =
                        mismatchErrors.get(new Pair<>(mte.expecting, mte.c));
                    final String msg = "Syntax error: " + (readable == null ? genericMsg : readable)
                        + " (" + mte.input.getSourceName() + ":" + mte.line + ")";
                    return new ProblemLoaderException(this, msg, mte);
                }
            }
        }
        // default
        return new ProblemLoaderException(this, "Loading proof input failed", e);
    }

    /**
     * Creates a new FileRepo (with or without consistency) based on the settings.
     *
     * @return a FileRepo that can be used for proof bundle saving
     * @throws IOException if for some reason the FileRepo can not be created (e.g. temporary
     *         directory can not be created).
     */
    protected FileRepo createFileRepo() throws IOException {
        // create a FileRepo depending on the settings
        boolean consistent = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .isEnsureSourceConsistency();

        if (consistent) {
            return new DiskFileRepo("KeYTmpFileRepo");
        } else {
            return new SimpleFileRepo();
        }
    }

    /**
     * Instantiates the {@link EnvInput} which represents the file to load.
     *
     * @param fileRepo the FileRepo used to ensure consistency between proof and source code
     * @return The created {@link EnvInput}.
     * @throws IOException Occurred Exception.
     */
    protected EnvInput createEnvInput(FileRepo fileRepo) throws IOException {

        final String filename = file.getName();

        // set the root directory of the FileRepo (used for resolving paths)
        fileRepo.setBaseDir(file.toPath());

        if (filename.endsWith(".java")) {
            // java file, probably enriched by specifications
            SLEnvInput ret = null;
            if (file.getParentFile() == null) {
                ret = new SLEnvInput(".", classPath, bootClassPath, profileOfNewProofs, includes);
            } else {
                ret = new SLEnvInput(file.getParentFile().getAbsolutePath(), classPath,
                    bootClassPath, profileOfNewProofs, includes);
            }
            ret.setJavaFile(file.getAbsolutePath());
            ret.setIgnoreOtherJavaFiles(loadSingleJavaFile);
            return ret;
        } else if (filename.endsWith(".zproof")) { // zipped proof package
            /*
             * TODO: Currently it is not possible to load proof bundles with multiple proofs. This
             * feature is still pending, since the functionality to save multiple proofs in one
             * (consistent!) package is not yet implemented (see ProofManagement tool from 1st
             * HacKeYthon). The current implementation allows the user to pick one of the proofs via
             * a dialog. The user choice is given to the AbstractProblem Loader via the proofName
             * field.
             */
            if (proofFilename == null) { // no proof to load given -> try to determine one
                // create a list of all *.proof files (only top level in bundle)
                List<Path> proofs;
                try (ZipFile bundle = new ZipFile(file)) {
                    proofs = bundle.stream().filter(e -> !e.isDirectory())
                            .filter(e -> e.getName().endsWith(".proof"))
                            .map(e -> Paths.get(e.getName())).collect(Collectors.toList());
                }
                if (!proofs.isEmpty()) {
                    // load first proof found in file
                    proofFilename = proofs.get(0).toFile();
                } else {
                    // no proof found in bundle!
                    throw new IOException("The bundle contains no proof to load!");
                }
            }

            // we are sure proofFilename is set now:
            // assert proofFilename != null;

            // unzip to a temporary directory
            Path tmpDir = Files.createTempDirectory("KeYunzip");
            IOUtil.extractZip(file.toPath(), tmpDir);

            // hook for deleting tmpDir + content at program exit
            Runtime.getRuntime().addShutdownHook(new Thread(() -> {
                try (Stream<Path> s = Files.walk(tmpDir)) {
                    // delete the temporary directory with all contained files
                    s.sorted(Comparator.reverseOrder()).map(Path::toFile)
                            .forEach(File::delete);
                } catch (IOException e) {
                    // this is called at program exist, so we only print a console message
                    LOGGER.warn("Failed to clean up temp dir", e);
                }
            }));

            // point the FileRepo to the temporary directory
            fileRepo.setBaseDir(tmpDir);

            // create new KeYUserProblemFile pointing to the (unzipped) proof file
            PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**.proof");

            // construct the absolute path to the unzipped proof file
            Path unzippedProof = tmpDir.resolve(proofFilename.toPath());

            return new KeYUserProblemFile(unzippedProof.toString(), unzippedProof.toFile(),
                fileRepo, control, profileOfNewProofs, false);
        } else if (filename.endsWith(".key") || filename.endsWith(".proof")
                || filename.endsWith(".proof.gz")) {
            // KeY problem specification or saved proof
            return new KeYUserProblemFile(filename, file, fileRepo, control, profileOfNewProofs,
                filename.endsWith(".proof.gz"));
        } else if (file.isDirectory()) {
            // directory containing java sources, probably enriched
            // by specifications
            return new SLEnvInput(file.getPath(), classPath, bootClassPath, profileOfNewProofs,
                includes);
        } else {
            if (filename.lastIndexOf('.') != -1) {
                throw new IllegalArgumentException("Unsupported file extension '"
                    + filename.substring(filename.lastIndexOf('.')) + "' of read-in file "
                    + filename + ". Allowed extensions are: .key, .proof, .java or "
                    + "complete directories.");
            } else {
                throw new FileNotFoundException(
                    "File or directory\n\t " + filename + "\n not found.");
            }
        }
    }

    /**
     * Instantiates the {@link ProblemInitializer} to use.
     *
     * @param fileRepo the FileRepo used to ensure consistency between proof and source code
     * @param registerProof Register loaded {@link Proof}
     * @return The {@link ProblemInitializer} to use.
     */
    protected ProblemInitializer createProblemInitializer(FileRepo fileRepo) {
        Profile profile = forceNewProfileOfNewProofs ? profileOfNewProofs : envInput.getProfile();
        ProblemInitializer pi = new ProblemInitializer(control, new Services(profile), control);
        pi.setFileRepo(fileRepo);
        return pi;
    }

    /**
     * Creates the {@link InitConfig}.
     *
     * @return The created {@link InitConfig}.
     * @throws ProofInputException Occurred Exception.
     */
    protected InitConfig createInitConfig() throws ProofInputException {
        return problemInitializer.prepare(envInput);
    }

    /**
     * Creates a {@link LoadedPOContainer} if available which contains the {@link ProofOblInput} for
     * which a {@link Proof} should be instantiated.
     *
     * @return The {@link LoadedPOContainer} or {@code null} if not available.
     * @throws IOException Occurred Exception.
     */
    protected LoadedPOContainer createProofObligationContainer() throws IOException {
        final String chooseContract;
        final String proofObligation;
        if (envInput instanceof KeYFile) {
            KeYFile keyFile = (KeYFile) envInput;
            chooseContract = keyFile.chooseContract();
            proofObligation = keyFile.getProofObligation();
        } else {
            chooseContract = null;
            proofObligation = null;
        }
        // Instantiate proof obligation
        if (envInput instanceof ProofOblInput && chooseContract == null
                && proofObligation == null) {
            return new LoadedPOContainer((ProofOblInput) envInput);
        } else if (chooseContract != null && chooseContract.length() > 0) {
            int proofNum = 0;
            String baseContractName;
            int ind = -1;
            for (String tag : FunctionalOperationContractPO.TRANSACTION_TAGS.values()) {
                ind = chooseContract.indexOf("." + tag);
                if (ind > 0) {
                    break;
                }
                proofNum++;
            }
            if (ind == -1) {
                baseContractName = chooseContract;
                proofNum = 0;
            } else {
                baseContractName = chooseContract.substring(0, ind);
            }
            final Contract contract = initConfig.getServices().getSpecificationRepository()
                    .getContractByName(baseContractName);
            if (contract == null) {
                throw new RuntimeException("Contract not found: " + baseContractName);
            } else {
                return new LoadedPOContainer(contract.createProofObl(initConfig), proofNum);
            }
        } else if (proofObligation != null && proofObligation.length() > 0) {
            // Load proof obligation settings
            final Properties properties = new Properties();
            properties.load(
                new ByteArrayInputStream(proofObligation.getBytes(StandardCharsets.UTF_8)));
            properties.setProperty(IPersistablePO.PROPERTY_FILENAME, file.getAbsolutePath());
            if (poPropertiesToForce != null) {
                properties.putAll(poPropertiesToForce);
            }
            String poClass = properties.getProperty(IPersistablePO.PROPERTY_CLASS);
            if (poClass == null || poClass.isEmpty()) {
                throw new IOException("Proof obligation class property \""
                    + IPersistablePO.PROPERTY_CLASS + "\" is not defiend or empty.");
            }
            try {
                // Try to instantiate proof obligation by calling static method: public static
                // LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws
                // IOException
                Class<?> poClassInstance = ClassLoaderUtil.getClassforName(poClass);
                Method loadMethod =
                    poClassInstance.getMethod("loadFrom", InitConfig.class, Properties.class);
                return (LoadedPOContainer) loadMethod.invoke(null, initConfig, properties);
            } catch (NoSuchMethodException | IllegalAccessException | IllegalArgumentException
                    | ClassNotFoundException e) {
                throw new IOException(
                    "Can't call static factory method \"loadFrom\" on class \"" + poClass + "\".",
                    e);
            } catch (InvocationTargetException e) {
                // Try to unwrap the inner exception as good as possible
                if (e.getCause() instanceof IOException) {
                    throw (IOException) e.getCause();
                } else if (e.getCause() instanceof RuntimeException) {
                    throw (RuntimeException) e.getCause();
                } else {
                    // Checked exception, just wrap it
                    throw new IOException(e);
                }
            }
        } else {
            return null;
        }
    }

    /**
     * Creates a {@link Proof} for the given {@link LoadedPOContainer} and tries to apply rules
     * again.
     *
     * @param poContainer The {@link LoadedPOContainer} to instantiate a {@link Proof} for.
     * @return The instantiated {@link Proof}.
     * @throws ProofInputException Occurred Exception.
     */
    protected ProofAggregate createProof(LoadedPOContainer poContainer) throws ProofInputException {

        ProofAggregate proofList =
            problemInitializer.startProver(initConfig, poContainer.getProofOblInput());

        for (Proof p : proofList.getProofs()) {
            // register proof
            initConfig.getServices().getSpecificationRepository()
                    .registerProof(poContainer.getProofOblInput(), p);
            initConfig.getFileRepo().registerProof(p);
        }

        return proofList;
    }

    /**
     * Run proof script if it is present in the input data.
     *
     * @return <code>true</code> iff there is a proof script to run
     */
    public boolean hasProofScript() {
        if (envInput instanceof KeYUserProblemFile) {
            KeYUserProblemFile kupf = (KeYUserProblemFile) envInput;
            return kupf.hasProofScript();
        }
        return false;
    }

    public Pair<String, Location> readProofScript() throws ProofInputException {
        assert envInput instanceof KeYUserProblemFile;
        KeYUserProblemFile kupf = (KeYUserProblemFile) envInput;

        Triple<String, Integer, Integer> script = kupf.readProofScript();
        URL url;
        try {
            url = kupf.getInitialFile().toURI().toURL();
        } catch (MalformedURLException e) {
            throw new ProofInputException(e);
        }
        Location location = new Location(url, Position.newOneBased(script.second, script.third));

        return new Pair<>(script.first, location);
    }

    public Pair<String, Location> getProofScript() throws ProblemLoaderException {
        if (hasProofScript()) {
            try {
                return readProofScript();
            } catch (ProofInputException e) {
                throw new ProblemLoaderException(this, e);
            }
        } else {
            return null;
        }
    }

    private ReplayResult replayProof(Proof proof)
            throws ProofInputException, ProblemLoaderException {
        LOGGER.info("Replaying proof " + proof.name());
        String status = "";
        List<Throwable> errors = new LinkedList<>();
        Node lastTouchedNode = proof.root();

        IntermediateProofReplayer replayer = null;
        IntermediatePresentationProofFileParser.Result parserResult = null;
        IntermediateProofReplayer.Result replayResult = null;

        final String ossStatus = (String) proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties().get(StrategyProperties.OSS_OPTIONS_KEY);
        ReplayResult result;
        try {
            assert envInput instanceof KeYUserProblemFile;

            IntermediatePresentationProofFileParser parser =
                new IntermediatePresentationProofFileParser(proof);
            problemInitializer.tryReadProof(parser, (KeYUserProblemFile) envInput);
            parserResult = parser.getResult();

            // Parser is no longer needed, set it to null to free memory.
            parser = null;

            // For loading, we generally turn on one step simplification to be
            // able to load proofs that used it even if the user has currently
            // turned OSS off.
            StrategyProperties newProps =
                proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_ON);
            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);

            replayer = new IntermediateProofReplayer(this, proof, parserResult);
            replayResult =
                replayer.replay(problemInitializer.getListener(), problemInitializer.getProgMon());

            lastTouchedNode = replayResult.getLastSelectedGoal() != null
                    ? replayResult.getLastSelectedGoal().node()
                    : proof.root();

        } catch (Exception e) {
            if (parserResult == null || parserResult.getErrors() == null
                    || parserResult.getErrors().isEmpty() || replayer == null
                    || replayResult == null || replayResult.getErrors() == null
                    || replayResult.getErrors().isEmpty()) {
                // this exception was something unexpected
                errors.add(e);
            }
        } finally {
            if (parserResult != null) {
                status = parserResult.getStatus();
                errors.addAll(parserResult.getErrors());
            }
            status +=
                (status.isEmpty() ? "" : "\n\n") + (replayResult != null ? replayResult.getStatus()
                        : "Error while loading proof.");
            if (replayResult != null) {
                errors.addAll(replayResult.getErrors());
            }

            StrategyProperties newProps =
                proof.getSettings().getStrategySettings().getActiveStrategyProperties();
            newProps.setProperty(StrategyProperties.OSS_OPTIONS_KEY, ossStatus);
            Strategy.updateStrategySettings(proof, newProps);
            OneStepSimplifier.refreshOSS(proof);

            result = new ReplayResult(status, errors, lastTouchedNode);
        }


        return result;
    }

    /**
     * Returns the file or folder to load.
     *
     * @return The file or folder to load.
     */
    public File getFile() {
        return file;
    }

    /**
     * Returns the optional class path entries to use.
     *
     * @return The optional class path entries to use.
     */
    public List<File> getClassPath() {
        return classPath;
    }

    /**
     * Returns the optional boot class path.
     *
     * @return The optional boot class path.
     */
    public File getBootClassPath() {
        return bootClassPath;
    }

    /**
     * Returns the instantiated {@link EnvInput} which describes the file to load.
     *
     * @return The instantiated {@link EnvInput} which describes the file to load.
     */
    public EnvInput getEnvInput() {
        return envInput;
    }

    /**
     * Returns the instantiated {@link ProblemInitializer} used during the loading process.
     *
     * @return The instantiated {@link ProblemInitializer} used during the loading process.
     */
    public ProblemInitializer getProblemInitializer() {
        return problemInitializer;
    }

    /**
     * Returns the instantiated {@link InitConfig} which provides access to the loaded source
     * elements and specifications.
     *
     * @return The instantiated {@link InitConfig} which provides access to the loaded source
     *         elements and specifications.
     */
    public InitConfig getInitConfig() {
        return initConfig;
    }

    /**
     * Returns the instantiate proof or {@code null} if no proof was instantiated during loading
     * process.
     *
     * @return The instantiate proof or {@code null} if no proof was instantiated during loading
     *         process.
     */
    public Proof getProof() {
        return proof;
    }

    /**
     * Returns the {@link ReplayResult} if available.
     *
     * @return The {@link ReplayResult} or {@code null} if not available.
     */
    public ReplayResult getResult() {
        return result;
    }

    public void setProofPath(File proofFilename) {
        this.proofFilename = proofFilename;
    }

    public boolean isLoadSingleJavaFile() {
        return loadSingleJavaFile;
    }

    public void setLoadSingleJavaFile(boolean loadSingleJavaFile) {
        this.loadSingleJavaFile = loadSingleJavaFile;
    }

    public void setIgnoreWarnings(boolean ignoreWarnings) {
        this.ignoreWarnings = ignoreWarnings;
    }
}