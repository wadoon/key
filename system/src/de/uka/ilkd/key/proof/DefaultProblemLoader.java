package de.uka.ilkd.key.proof;

import java.io.File;
import java.io.IOException;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.proof.init.AbstractProblemInitializer;
import de.uka.ilkd.key.proof.init.IPersistablePO.LoadedPOContainer;
import de.uka.ilkd.key.proof.init.IProofReader;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaDLInitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.DefaultProofFileParser;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.io.IKeYFile;

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
   protected EnvInput<S, IC> envInput;
   
   /**
    * The instantiated {@link ProblemInitializer} used during the loading process.
    */
   protected AbstractProblemInitializer<S, IC> problemInitializer;
   
   /**
    * The instantiated {@link JavaDLInitConfig} which provides access to the loaded source elements and specifications.
    */
   protected IC initConfig;
   
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
   public String load() throws ProblemLoaderException {
      try {
         // Read environment
      boolean oneStepSimplifier = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().oneStepSimplification();
      ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setOneStepSimplification(true);
         envInput = createEnvInput();
         problemInitializer = createProblemInitializer();
         initConfig = createInitConfig();
         // Read proof obligation settings
         LoadedPOContainer poContainer = createProofObligationContainer();
         try {
            if (poContainer == null) {
               return selectProofObligation();
            }
            // Create proof and apply rules again if possible
            proof = createProof(poContainer);
            if (proof != null) {
               replayProof(proof);
            }
            return ""; // Everything fine
         }
         finally {
    	  ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setOneStepSimplification(oneStepSimplifier);
            getMediator().resetNrGoalsClosedByHeuristics();
            if (poContainer != null && poContainer.getProofOblInput() instanceof IKeYFile) {
               ((IKeYFile<S, IC>)poContainer.getProofOblInput()).close();
            }  
         }
      }
      catch (Exception e) {
         throw new ProblemLoaderException(this, e);
      }
   }

    protected abstract Proof createProof(LoadedPOContainer poContainer) throws ProofInputException;

    protected abstract LoadedPOContainer createProofObligationContainer() throws IOException;

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
    * This method is called if no {@link LoadedPOContainer} was created
    * via {@link #createProofObligationContainer()} and can be overwritten
    * for instance to open the proof management dialog as done by {@link ProblemLoader}.
    * @return An error message or {@code null} if everything is fine.
    */
   protected abstract String selectProofObligation();


   protected void replayProof(Proof proof) throws ProofInputException {
      mediator.setProof(proof);

      mediator.stopInterface(true); // first stop (above) is not enough

      if (envInput instanceof IProofReader) {
         problemInitializer.tryReadProof(new DefaultProofFileParser(proof, mediator),
                 (IProofReader) envInput);
      }
      mediator.getUI().resetStatus(this);
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
