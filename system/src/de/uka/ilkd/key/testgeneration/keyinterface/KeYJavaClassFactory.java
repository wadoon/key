package de.uka.ilkd.key.testgeneration.keyinterface;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.testgeneration.TestGeneratorException;

/**
 * Produces instances of {@link KeYJavaClass}.
 * 
 * @author christopher
 */
public enum KeYJavaClassFactory {
    INSTANCE;

    /**
     * The singleton {@link KeYInterface}, used in order to communicate with the KeY runtime.
     */
    private final KeYInterface keyInterface = KeYInterface.INSTANCE;
    
    public KeYJavaClass createKeYJavaClass(String absolutePath) throws IOException, KeYInterfaceException {

        /*
         * Load the file into key and set the InitConfig instance for it.
         */
        File javaFile = loadFile(absolutePath);
        InitConfig initConfig = keyInterface.loadJavaFile(javaFile);

        JavaInfo javaInfo = initConfig.getServices().getJavaInfo();

        /*
         * Retrieve the KeYJavaType for the top level class declaration in this file
         */
        String fileName = getFileName(javaFile);
        KeYJavaType mainClass = javaInfo.getKeYJavaType(fileName);

        /*
         * Extract all methods declared in this class (including the ones provided in
         * Java.lang.Object, even if these have not been overridden), and create name-value mappings
         * for them. Exclude implicit methods (i.e. <create>, <init> etc).
         */
        HashMap<String, KeYJavaMethod> methods =
                new HashMap<String, KeYJavaMethod>();
        
        for (IProgramMethod method : javaInfo.getAllProgramMethods(mainClass)) {
            if (!method.getFullName().startsWith("<")) {
                KeYJavaMethod keYJavaMethod = new KeYJavaMethod(method, initConfig, null);
                methods.put(method.getFullName(), keYJavaMethod);
            }
        }
        
        return new KeYJavaClass(mainClass, methods);
    }

    /**
     * Retrieve a {@link File} reference to the .java file selected by the user.
     * 
     * @param path
     * @return
     * @throws TestGeneratorException
     * @throws IOException
     */
    private File loadFile(String path) throws IOException {

        File javaFile = new File(path);
        if (!javaFile.exists()) {
            throw new IOException("FATAL: no such file or directory: " + path);
        }
        return javaFile;
    }

    /**
     * Strips the file extension from a file name
     * 
     * @param file
     *            the file to process
     * @return the name of the file
     */
    private String getFileName(File file) {

        String name = file.getName();
        int delimiter = name.indexOf('.');
        return name.substring(0, delimiter);
    }
}
