package de.uka.ilkd.key.proof.io;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.FileProblemLoader.ReplayResult;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.Contract;

/**
 * Common code of the problem loaders {@link FileProblemLoader} and
 * {@link StringProblemLoader}.
 * 
 * @author Kai Wallisch
 *
 */
public abstract class AbstractProblemLoader {

    protected AbstractProblemLoader(ProblemLoaderControl control) {
        this.control = control;
    }

    /**
     * The {@link ProblemLoaderControl} to use.
     */
    protected final ProblemLoaderControl control;

    /**
     * The instantiated {@link EnvInput} which describes the file to load.
     */
    protected EnvInput envInput;

    /**
     * The instantiated {@link ProblemInitializer} used during the loading process.
     */
    protected ProblemInitializer problemInitializer;

    /**
     * The instantiated {@link InitConfig} which provides access to the loaded source elements and specifications.
     */
    protected InitConfig initConfig;

    /**
     * The instantiate proof or {@code null} if no proof was instantiated during loading process.
     */
    protected Proof proof;

    /**
     * The {@link ReplayResult} if available or {@code null} otherwise.
     */
    protected ReplayResult replayResult;

    /**
     * Returns the instantiated {@link InitConfig} which provides access to the
     * loaded source elements and specifications.
     * 
     * @return The instantiated {@link InitConfig} which provides access to the
     *         loaded source elements and specifications.
     */
    public InitConfig getInitConfig() {
        return initConfig;
    }

    /**
     * Returns the instantiate proof or {@code null} if no proof was
     * instantiated during loading process.
     * 
     * @return The instantiate proof or {@code null} if no proof was
     *         instantiated during loading process.
     */
    public Proof getProof() {
        return proof;
    }

    protected abstract ProofAggregate createProofAggregate(LoadedPOContainer poContainer) throws ProofInputException, ProblemLoaderException;

    protected abstract EnvInput createEnvInput() throws IOException;

    protected abstract ProblemInitializer createProblemInitializer();

    /**
     * Executes the loading process and tries to instantiate a proof and to
     * re-apply rules on it if possible.
     * 
     * @throws ProofInputException
     *             Occurred Exception.
     * @throws IOException
     *             Occurred Exception.
     * @throws ProblemLoaderException
     *             Occurred Exception.
     */
    public final void load() throws ProblemLoaderException, ProofInputException, IOException {
        control.loadingStarted(this);
        // Read environment
        envInput = createEnvInput();
        problemInitializer = createProblemInitializer();
        initConfig = problemInitializer.prepare(envInput);
        if (!problemInitializer.getWarnings().isEmpty()) {
            control.reportWarnings(problemInitializer.getWarnings());
        }
        // Read proof obligation settings
        LoadedPOContainer poContainer = createProofObligationContainer();
        ProofAggregate proofList = null;
        try {
            proofList = createProofAggregate(poContainer);
            if (proofList != null && poContainer != null) {
                proof = proofList.getProof(poContainer.getProofNum());
                // try to replay first proof
                if (proof != null && envInput instanceof AbstractKeYParserEnvInput) {
                    OneStepSimplifier.refreshOSS(proof);
                    replayResult = replayProof(proof, (AbstractKeYParserEnvInput) envInput);
                }
            }
        } finally {
            control.loadingFinished(this, poContainer, proofList, replayResult);
        }
    }
    
    private ReplayResult replayProof(Proof proof, AbstractKeYParserEnvInput parserEnvInput) throws ProofInputException, ProblemLoaderException {
        String status = "";
        List<Throwable> errors = new LinkedList<Throwable>();
        Node lastTouchedNode = proof.root();
        
        IProofFileParser parser = null;
        IntermediateProofReplayer replayer = null;
        IntermediatePresentationProofFileParser.Result parserResult = null;
        IntermediateProofReplayer.Result replayResult = null;

        final boolean isOSSActivated =
                ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().oneStepSimplification();
        ReplayResult result;
        try {
                
                parser = new IntermediatePresentationProofFileParser(proof);
                problemInitializer.tryReadProof(parser, parserEnvInput);
                parserResult = ((IntermediatePresentationProofFileParser) parser).getResult();
                
                // Parser is no longer needed, set it to null to free memory.
                parser = null;
                
                // For loading, we generally turn on one step simplification to be
                // able to load proofs that used it even if the user has currently
                // turned OSS off.
                ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setOneStepSimplification(true);
                OneStepSimplifier.refreshOSS(proof);
                
                replayer = new IntermediateProofReplayer(this, proof, parserResult);
                replayResult = replayer.replay();
                
                lastTouchedNode = replayResult.getLastSelectedGoal() != null ? replayResult.getLastSelectedGoal().node() : proof.root();

        } catch (Exception e) {
            if (parserResult == null || parserResult.getErrors() == null || parserResult.getErrors().isEmpty() ||
                    replayer == null || replayResult == null || replayResult.getErrors() == null || replayResult.getErrors().isEmpty()) {
                // this exception was something unexpected
                errors.add(e);
            }
        } finally {
            if (parserResult != null) {
                status = parserResult.getStatus();
                errors.addAll(parserResult.getErrors());
            }
            status += (status.isEmpty() ? "" : "\n\n") + (replayResult != null ? replayResult.getStatus() : "Error while loading proof.");
            if (replayResult != null) {
                errors.addAll(replayResult.getErrors());
            }
            
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setOneStepSimplification(isOSSActivated);
            OneStepSimplifier.refreshOSS(proof);
            result = new ReplayResult(status, errors, lastTouchedNode);
        }
            
        
        return result;
    }
    
    protected abstract LoadedPOContainer createProofObligationContainerFromJavaClass(String proofObligation) throws IOException;
    
    /**
     * Creates a {@link LoadedPOContainer} if available which contains
     * the {@link ProofOblInput} for which a {@link Proof} should be instantiated.
     * @return The {@link LoadedPOContainer} or {@code null} if not available.
     * @throws IOException Occurred Exception.
     */
    protected LoadedPOContainer createProofObligationContainer() throws IOException {
        final String chooseContract;
        final String proofObligation;
        if (envInput instanceof KeYFile) {
            KeYFile keyFile = (KeYFile)envInput;
            chooseContract = keyFile.chooseContract();
            proofObligation = keyFile.getProofObligation();
        }
        else {
            chooseContract = null;
            proofObligation = null;
        }
        // Instantiate proof obligation
        if (envInput instanceof ProofOblInput && chooseContract == null && proofObligation == null) {
            return new LoadedPOContainer((ProofOblInput)envInput);
        }
        else if (chooseContract != null && chooseContract.length() > 0) {
            int proofNum = 0;
            String baseContractName = null;
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
            }
            else {
                baseContractName = chooseContract.substring(0, ind);
            }
            final Contract contract = initConfig.getServices().getSpecificationRepository().getContractByName(baseContractName);
            if (contract == null) {
                throw new RuntimeException("Contract not found: " + baseContractName);
            }
            else {
                return new LoadedPOContainer(contract.createProofObl(initConfig), proofNum);
            }
        }
        else if (proofObligation != null && proofObligation.length() > 0) {
            return createProofObligationContainerFromJavaClass(proofObligation);
        }
        else {
            return null;
        }
    }

}
