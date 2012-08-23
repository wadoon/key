package de.uka.ilkd.key.proof;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.speclang.Contract;

/**
 * <p>
 * This class provides the functionality to load something it KeY.
 * The loading process is done in the current {@link Thread} and 
 * no user interaction is required.
 * </p>
 * <p>
 * The basic usage of this class is to instantiate a new {@link DefaultProblemLoader}
 * instance with should load the file configured by the constructor's arguments.
 * The next step is to call {@link #load()} which does the loading process and
 * tries to instantiate a proof and to apply rules again if possible. The result
 * of the loading process is available via the getter methods.
 * </p>
 * @author Martin Hentschel
 */
public abstract class DefaultProblemLoader<S extends IServices, IC extends InitConfig<S, IC>> {
   /**
    * The file or folder to load.
    */
   protected File file;
   
   /**
    * The optional class path entries to use.
    */
   protected List<File> classPath;
   
   /**
    * An optional boot class path.
    */
   protected File bootClassPath;

   /**
    * The {@link KeYMediator} to use.
    */
   protected KeYMediator<S, IC> mediator;
   
   /**
    * The instantiated {@link EnvInput} which describes the file to load.
    */
   private EnvInput<S, IC> envInput;
   
   /**
    * The instantiated {@link ProblemInitializer} used during the loading process.
    */
   private  AbstractProblemInitializer<S, IC> problemInitializer;
   
   /**
    * The instantiated {@link JavaDLInitConfig} which provides access to the loaded source elements and specifications.
    */
   private IC initConfig;
   
   /**
    * The instantiate proof or {@code null} if no proof was instantiated during loading process.
    */
   private Proof proof;

   /**
    * Constructor.
    * @param file The file or folder to load.
    * @param classPath The optional class path entries to use.
    * @param bootClassPath An optional boot class path.
    * @param mediator The {@link KeYMediator} to use.
    */
   public DefaultProblemLoader(File file, List<File> classPath, File bootClassPath, KeYMediator<S, IC> mediator) {
      assert mediator != null;
      this.file = file;
      this.classPath = classPath;
      this.bootClassPath = bootClassPath;
      this.mediator = mediator;
   }

   /**
    * Executes the loading process and tries to instantiate a proof
    * and to re-apply rules on it if possible. 
    * @return An error message or {@code ""} (empty string) if everything is fine.
    * @throws ProofInputException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public String load() throws ProofInputException, IOException {
      // Read environment
      envInput = createEnvInput();
      problemInitializer = createProblemInitializer();
      initConfig = createInitConfig();
      // Read proof obligation settings
      LoadedPOContainer poContainer = createProofObligationContainer();
      if (poContainer == null) {
         return selectProofObligation();
      }
      // Create proof and apply rules again if possible
      proof = createProof(poContainer);
      return ""; // Everything fine
   }

   /**
    * Instantiates the {@link EnvInput} which represents the file to load.
    * @return The created {@link EnvInput}.
    * @throws IOException Occurred Exception.
    */
   protected abstract EnvInput<S, IC> createEnvInput() throws IOException;
   
   /**
    * Instantiates the {@link ProblemInitializer} to use.
    * @return The {@link ProblemInitializer} to use.
    */
   protected AbstractProblemInitializer<S, IC> createProblemInitializer() {
       return mediator.getUI().createProblemInitializer(true);
   }
   
   /**
    * Creates the {@link JavaDLInitConfig}.
    * @return The created {@link JavaDLInitConfig}.
    * @throws ProofInputException Occurred Exception.
    */
   protected IC createInitConfig() throws ProofInputException {
      return problemInitializer.prepare(envInput);
   }
   
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
            return new LoadedPOContainer(contract.createProofObl(initConfig, contract), proofNum);
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
            return (LoadedPOContainer)loadMethod.invoke(null, initConfig, properties);
         }
         catch (Exception e) {
            throw new IOException("Can't call static factory method \"loadFrom\" on class \"" + poClass + "\".", e);
         }
      }
      else {
         return null;
      }
   }

   /**
    * This method is called if no {@link LoadedPOContainer} was created
    * via {@link #createProofObligationContainer()} and can be overwritten
    * for instance to open the proof management dialog as done by {@link ProblemLoader}.
    * @return An error message or {@code null} if everything is fine.
    */
   protected String selectProofObligation() {
      return null; // Do nothing
   }

   /**
    * Creates a {@link Proof} for the given {@link LoadedPOContainer} and
    * tries to apply rules again.
    * @param poContainer The {@link LoadedPOContainer} to instantiate a {@link Proof} for.
    * @return The instantiated {@link Proof}.
    * @throws ProofInputException Occurred Exception.
    */
   protected Proof createProof(LoadedPOContainer poContainer) throws ProofInputException {
      mediator.setProof(problemInitializer.startProver(initConfig, poContainer.getProofOblInput(), poContainer.getProofNum()));

      Proof proof = mediator.getSelectedProof();
      mediator.stopInterface(true); // first stop (above) is not enough

      if (envInput instanceof KeYUserProblemFile) {
         problemInitializer.tryReadProof(new DefaultProofFileParser(proof, mediator), (KeYUserProblemFile) envInput);
      }
      mediator.getUI().resetStatus(this);
      return proof;
   }

   /**
    * Returns the file or folder to load.
    * @return The file or folder to load.
    */
   public File getFile() {
      return file;
   }

   /**
    * Returns the optional class path entries to use.
    * @return The optional class path entries to use.
    */
   public List<File> getClassPath() {
      return classPath;
   }

   /**
    * Returns the optional boot class path.
    * @return The optional boot class path.
    */
   public File getBootClassPath() {
      return bootClassPath;
   }

   /**
    * Returns the {@link KeYMediator} to use.
    * @return The {@link KeYMediator} to use.
    */
   public KeYMediator<S, IC> getMediator() {
      return mediator;
   }

   /**
    * Returns the instantiated {@link EnvInput} which describes the file to load.
    * @return The instantiated {@link EnvInput} which describes the file to load.
    */
   public EnvInput<S, IC> getEnvInput() {
      return envInput;
   }
   
   /**
    * Returns the instantiated {@link ProblemInitializer} used during the loading process.
    * @return The instantiated {@link ProblemInitializer} used during the loading process.
    */
   public AbstractProblemInitializer<S,IC> getProblemInitializer() {
      return problemInitializer;
   }

   /**
    * Returns the instantiated {@link JavaDLInitConfig} which provides access to the loaded source elements and specifications.
    * @return The instantiated {@link JavaDLInitConfig} which provides access to the loaded source elements and specifications.
    */
   public IC getInitConfig() {
      return initConfig;
   }

   /**
    * Returns the instantiate proof or {@code null} if no proof was instantiated during loading process.
    * @return The instantiate proof or {@code null} if no proof was instantiated during loading process.
    */
   public Proof getProof() {
      return proof;
   }
}
