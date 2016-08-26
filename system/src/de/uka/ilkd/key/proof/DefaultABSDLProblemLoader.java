package de.uka.ilkd.key.proof;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.JavaDLInitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.gui.POBrowserData;
import de.uka.ilkd.keyabs.gui.ProofObligationChooser;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.proof.init.ABSKeYUserProblemFile;
import de.uka.ilkd.keyabs.proof.io.ABSKeYFile;
import de.uka.ilkd.keyabs.speclang.ABSSLInput;

public class DefaultABSDLProblemLoader extends
        ProblemLoader<ABSServices, ABSInitConfig> {

    private String poID;

    public DefaultABSDLProblemLoader(File file, List<File> classPath,
            File bootClassPath, KeYMediator<ABSServices, ABSInitConfig> mediator) {
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

/*
    @Override
    protected Proof createProof(IPersistablePO.LoadedPOContainer poContainer) throws ProofInputException {
        mediator.setProof(problemInitializer.startProver(initConfig, poContainer.getProofOblInput(), poContainer.getProofNum()));

        Proof proof = mediator.getSelectedProof();
        mediator.stopInterface(true); // first stop (above) is not enough

        if (envInput instanceof ABSKeYUserProblemFile) {
           // problemInitializer.tryReadProof(new DefaultProofFileParser(proof, mediator),
             //       (ABSKeYUserProblemFile) envInput);
        }
        mediator.getUI().resetStatus(this);
        return proof;
    }
*/

    @Override
    protected IPersistablePO.LoadedPOContainer createProofObligationContainer() throws IOException {
        final String chooseContract;
        final String proofObligation;
        if (envInput instanceof ABSKeYFile) {
        	ABSKeYFile keyFile = (ABSKeYFile)envInput;
            chooseContract = keyFile.chooseContract();
            proofObligation = keyFile.getProofObligation();
        }
        else {
            chooseContract = null;
            proofObligation = null;
        }    	
    	if (envInput instanceof ProofOblInput && chooseContract == null && proofObligation == null) {
    			return new IPersistablePO.LoadedPOContainer((ProofOblInput)envInput);
        } else if (proofObligation != null && proofObligation.length() > 0) {
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
                Method loadMethod = poClassInstance.getMethod("loadFrom", ABSInitConfig.class, Properties.class);
                return (IPersistablePO.LoadedPOContainer)loadMethod.invoke(null, initConfig, properties);
            }
            catch (Exception e) {
                throw new IOException("Can't call static factory method \"loadFrom\" on class \"" + poClass + "\".", e);
            }
        }
        return null;
    }

    @Override
    protected EnvInput<ABSServices, ABSInitConfig> createEnvInput() throws IOException {
    
          final String filename = file.getName();
          if (filename.endsWith(".key") || filename.endsWith(".proof")) {
                  return new ABSKeYUserProblemFile(filename, file, mediator.getUI());
          } else if (file.isDirectory()) {
              return new ABSSLInput(file.getPath(), classPath, bootClassPath);
          } else {
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

    @Override
    protected String selectProofObligation() {
        POBrowserData data = new POBrowserData(getInitConfig().getServices());
        ProofObligationChooser chooser =
                new ProofObligationChooser(getMediator(), getInitConfig(), data);

        return chooser.isProofStarted() ? "" : "Aborted.";
    }
}
