package de.uka.ilkd.key.gui.lemmatagenerator;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.AbstractProblemInitializer.ProblemInitializerListener;
import de.uka.ilkd.key.proof.io.IKeYFile;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.util.ProgressMonitor;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.proof.init.ABSInitConfig;
import de.uka.ilkd.keyabs.proof.init.ABSProblemInitializer;
import de.uka.ilkd.keyabs.proof.init.ABSKeYUserProblemFile;

public class EnvironmentCreator<S extends IServices, IC extends InitConfig<S,IC>>  {
        
        private IKeYFile<S,IC> keyFile;
        
        public IKeYFile<S, IC> getKeyFile() {
                if(keyFile == null){
                        throw new IllegalStateException("You must call the method create before");
                }
                return keyFile;
        }
        
        
        public ProofEnvironment<IC> create(String pathForDummyFile,ProgressMonitor monitor,
                          ProblemInitializerListener<S,IC> listener, Profile<S,IC> profile) throws IOException,
        ProofInputException {
                File dummyFile = createDummyKeYFile(pathForDummyFile);
                keyFile = (IKeYFile<S, IC>) (profile instanceof JavaProfile ? 
                             new KeYUserProblemFile(
                                dummyFile.getName(), dummyFile, null) :
                             new ABSKeYUserProblemFile(
                                dummyFile.getName(), dummyFile, null));

                final AbstractProblemInitializer<S, IC> pi = 
                        (AbstractProblemInitializer<S, IC>) (profile instanceof JavaProfile ?
                        new ProblemInitializer(monitor, (Profile<Services, JavaDLInitConfig>)profile, false, 
                                (ProblemInitializerListener<Services, JavaDLInitConfig>)listener) :
                            new ABSProblemInitializer(monitor, (Profile<ABSServices, ABSInitConfig>) profile, false, 
                                    (ProblemInitializerListener<ABSServices, ABSInitConfig>)listener ));
               
                return pi.prepare(keyFile).getProofEnv();
        }

        public File createDummyKeYFile(String pathForDummyFile) throws IOException {
                File file = new File(pathForDummyFile + File.separator
                                + "lemmataGenDummy.key");
                file.deleteOnExit();
                String s = "\\problem{true}";
                FileWriter writer = new FileWriter(file);
                writer.write(s);
                writer.close();
                return file;
        }
}
