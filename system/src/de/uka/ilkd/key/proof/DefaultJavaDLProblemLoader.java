package de.uka.ilkd.key.proof;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.init.JavaDLInitConfig;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.speclang.SLEnvInput;

public class DefaultJavaDLProblemLoader extends
        DefaultProblemLoader<Services, JavaDLInitConfig> {

    public DefaultJavaDLProblemLoader(File file, List<File> classPath,
            File bootClassPath, KeYMediator<Services, JavaDLInitConfig> mediator) {
        super(file, classPath, bootClassPath, mediator);
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
    
}
