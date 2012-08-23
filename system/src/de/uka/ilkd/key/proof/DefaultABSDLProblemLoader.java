package de.uka.ilkd.key.proof;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.init.ABSInitConfig;
import de.uka.ilkd.keyabs.po.ABSKeYUserProblemFile;

public class DefaultABSDLProblemLoader extends
        DefaultProblemLoader<ABSServices, ABSInitConfig> {

    public DefaultABSDLProblemLoader(File file, List<File> classPath,
            File bootClassPath, KeYMediator<ABSServices, ABSInitConfig> mediator) {
        super(file, classPath, bootClassPath, mediator);
    }

    @Override
    protected EnvInput<ABSServices, ABSInitConfig> createEnvInput() throws IOException {
    
          final String filename = file.getName();
    
          if (filename.endsWith(".key") || filename.endsWith(".proof")) {
                  return new ABSKeYUserProblemFile(filename, file, mediator.getUI());
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

}
