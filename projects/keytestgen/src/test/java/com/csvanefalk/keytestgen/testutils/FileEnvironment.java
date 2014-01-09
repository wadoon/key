package com.csvanefalk.keytestgen.testutils;

import org.junit.Assert;

import java.io.File;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class FileEnvironment {

    public static FileEnvironment constructFileEnvironment(String directory, boolean includeSubdirectories) {

        List<File> javaFiles = loadAllJavaFilesInDirectory(directory, includeSubdirectories);

        Map<String, File> sourceFiles = new HashMap<String, File>();
        for (File file : javaFiles) {
            String name = file.getName();
            name = name.substring(0, name.indexOf("."));
            sourceFiles.put(name, file);
        }

        return new FileEnvironment(sourceFiles);
    }

    public static FileEnvironment constructFileEnvironment(String directory,
                                                           final boolean includeSubdirectories,
                                                           String... files) {

        List<File> javaFiles;

        if (files.length == 0) {
            javaFiles = loadAllJavaFilesInDirectory(directory, includeSubdirectories);
        } else {
            //Filter out all non-desired files
            javaFiles = new LinkedList<File>();
            for (File file : loadAllJavaFilesInDirectory(directory, includeSubdirectories)) {
                for (String acceptedFileName : files) {
                    if (file.getName().equalsIgnoreCase(acceptedFileName)) {
                        javaFiles.add(file);
                        break;
                    }
                }
            }
        }

        Map<String, File> sourceFiles = new HashMap<String, File>();
        for (File file : javaFiles) {
            String name = file.getName();
            name = name.substring(0, name.indexOf("."));
            sourceFiles.put(name, file);
        }

        return new FileEnvironment(sourceFiles);
    }

    /**
     * Absolute path inside the KeYTestGen root folder to the repository of test
     * models.
     */
    protected final static String targetModelsPath = "src/test/java/com/csvanefalk/keytestgen/targetmodels/";

    /**
     * Relative OS path to the KeYTestGen folder.
     */
    protected final static String keYTestGenPath = System.getProperty("user.dir") + "/";

    /**
     * Source files contained in this environment.
     */
    private final Map<String, File> sourceFiles;

    public FileEnvironment(Map<String, File> sourceFiles) {
        super();
        this.sourceFiles = sourceFiles;
    }

    /**
     * Gets file handlers for all Java files in a directory.
     *
     * @param directory
     * @param includeSubdirectories
     * @return
     */
    private static List<File> loadAllJavaFilesInDirectory(String directory, boolean includeSubdirectories) {
        List<File> results = new LinkedList<File>();

        String path = keYTestGenPath + targetModelsPath + directory;
        File folder = new File(path);
        File[] files = folder.listFiles();
        for (int i = 0; i < files.length; i++) {
            File file = files[i];
            Assert.assertNotNull(file);

            /*
             * If the file is an ordinary file, add it iff it is a Java file.
             */
            if (file.isFile()) {
                if (file.getName().endsWith(".java")) {
                    Assert.assertTrue(file.canRead());
                    results.add(files[i]);
                }
            }

            /*
             * If it is a directory and we have the includeSubdirectories flag
             * set, add all files from the subdirectory.
             */
            else if (file.isDirectory() && includeSubdirectories) {
                String subpath = directory + File.separator + file.getName() + File.separator;
                List<File> filesFromSubdirectory = loadAllJavaFilesInDirectory(subpath, includeSubdirectories);
                results.addAll(filesFromSubdirectory);
            }
        }
        return results;
    }

    public File getFile(String name) {
        return sourceFiles.get(name);
    }

    public List<String> getFileNames() {
        List<String> fileNames = new LinkedList<String>();
        fileNames.addAll(sourceFiles.keySet());
        return fileNames;
    }

    public List<File> getFiles() {
        List<File> files = new LinkedList<File>();
        files.addAll(sourceFiles.values());
        return files;
    }
}
