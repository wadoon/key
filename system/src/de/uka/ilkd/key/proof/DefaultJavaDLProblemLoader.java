package de.uka.ilkd.key.proof;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.JavaDLInitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.IKeYFile;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.SLEnvInput;

public class DefaultJavaDLProblemLoader extends
        ProblemLoader<Services, JavaDLInitConfig> {

    public DefaultJavaDLProblemLoader(File file, List<File> classPath,
            File bootClassPath, KeYMediator<Services, JavaDLInitConfig> mediator) {
        super(file, classPath, bootClassPath, mediator);
    }


    /**
     * Creates a {@link Proof} for the given {@link de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer} and
     * tries to apply rules again.
     * @param poContainer The {@link de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer} to instantiate a {@link Proof} for.
     * @return The instantiated {@link Proof}.
     * @throws ProofInputException Occurred Exception.
     */
    protected Proof createProof(IPersistablePO.LoadedPOContainer poContainer) throws ProofInputException {
        return problemInitializer.startProver(initConfig, poContainer.getProofOblInput(), poContainer.getProofNum());
    }


    /**
     * Creates a {@link Proof} for the given {@link de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer} and
     * tries to apply rules again.
     * @param poContainer The {@link de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer} to instantiate a {@link Proof} for.
     * @return The instantiated {@link Proof}.
     * @throws de.uka.ilkd.key.proof.init.ProofInputException Occurred Exception.
     */
/*    protected Proof createProof(IPersistablePO.LoadedPOContainer poContainer) throws ProofInputException {
        mediator.setProof(problemInitializer.startProver(initConfig, poContainer.getProofOblInput(), poContainer.getProofNum()));

        Proof proof = mediator.getSelectedProof();
        mediator.stopInterface(true); // first stop (above) is not enough

        if (envInput instanceof KeYUserProblemFile) {
            problemInitializer.tryReadProof(new DefaultProofFileParser(proof, mediator), (KeYUserProblemFile) envInput);
        }
        mediator.getUI().resetStatus(this);
        return proof;
    }*/


    /**
     * Creates a {@link de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer} if available which contains
     * the {@link de.uka.ilkd.key.proof.init.ProofOblInput} for which a {@link Proof} should be instantiated.
     * @return The {@link de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer} or {@code null} if not available.
     * @throws IOException Occurred Exception.
     */
    protected IPersistablePO.LoadedPOContainer createProofObligationContainer() throws IOException {
        final String chooseContract;
        final String proofObligation;
        if (envInput instanceof IKeYFile) {
        	IKeYFile<Services, JavaDLInitConfig> keyFile = (IKeYFile<Services, JavaDLInitConfig>) envInput;
            chooseContract = keyFile.chooseContract();
            proofObligation = keyFile.getProofObligation();
        }
        else {
            chooseContract = null;
            proofObligation = null;
        }
        // Instantiate proof obligation
        if (envInput instanceof ProofOblInput && chooseContract == null && proofObligation == null) {
            return new IPersistablePO.LoadedPOContainer((ProofOblInput)envInput);
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
                return new IPersistablePO.LoadedPOContainer(contract.createProofObl(initConfig, contract), proofNum);
            }
        }
        else if (proofObligation != null && proofObligation.length() > 0) {
            // Load proof obligation settings
            Properties properties = new Properties();
            properties.load(new ByteArrayInputStream(proofObligation.getBytes()));
            String poClass = properties.getProperty(IPersistablePO.PROPERTY_CLASS);
            if (poClass == null || poClass.isEmpty()) {
                throw new IOException("Proof obligation class property \"" + IPersistablePO.PROPERTY_CLASS + "\" is not defiend or empty.");
            }
            try {
                // Try to instantiate proof obligation by calling static method: public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException
                Class<?> poClassInstance = Class.forName(poClass);
                Method loadMethod = poClassInstance.getMethod("loadFrom", JavaDLInitConfig.class, Properties.class);
                return (IPersistablePO.LoadedPOContainer)loadMethod.invoke(null, initConfig, properties);
            }
            catch (Exception e) {
                throw new IOException("Can't call static factory method \"loadFrom\" on class \"" + poClass + "\".", e);
            }
        }
        else {
            return null;
        }
    }


    @Override
    protected EnvInput<Services, JavaDLInitConfig> createEnvInput() throws IOException {
    
          final String filename = file.getName();
    
          if (filename.endsWith(".java")) {
             // java file, probably enriched by specifications
             if (file.getParentFile() == null) {
                return (EnvInput<Services, JavaDLInitConfig>) new SLEnvInput(".", classPath, bootClassPath);
             }
             else {
                return (EnvInput<Services, JavaDLInitConfig>) new SLEnvInput(file.getParentFile().getAbsolutePath(),
                      classPath, bootClassPath);
             }
          }
          else if (filename.endsWith(".key") || filename.endsWith(".proof")) {
        	  // KeY problem specification or saved proof
             return new KeYUserProblemFile(filename, file, mediator.getUI());
          }
          else if (file.isDirectory()) {
             // directory containing java sources, probably enriched
             // by specifications
             return (EnvInput<Services, JavaDLInitConfig>) new SLEnvInput(file.getPath(), classPath, bootClassPath);
          }
          else {
             if (filename.lastIndexOf('.') != -1) {
                throw new IllegalArgumentException("Unsupported file extension \'"
                      + filename.substring(filename.lastIndexOf('.'))
                      + "\' of read-in file " + filename
                      + ". Allowed extensions are: .key, .proof, .java or "
                      + "complete directories.");
             }
             else {
                throw new FileNotFoundException("File or directory\n\t " + filename
                      + "\n not found.");
             }
          }
       }


    protected String selectProofObligation() {
        ProofManagementDialog.showInstance(getMediator(), getInitConfig());
        if (ProofManagementDialog.startedProof()) {
            return "";
        }
        else {
            return "Aborted.";
        }
    }
    
}
