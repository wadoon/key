//This file is part of the RECODER library and protected by the LGPL.

package recoder.testsuite.testsuite.basic;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestResult;
import junit.framework.TestSuite;
import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.io.DefaultProjectFileIO;
import recoder.io.SourceFileRepository;
import recoder.java.CompilationUnit;
import recoder.service.DefaultErrorHandler;
import recoder.service.SemanticsChecker;

/**
 * Call example: java test.TransformationTests standard.tst collections.prj
 */

public class BasicTestsSuite extends TestSuite {

    public static CrossReferenceServiceConfiguration config;

    private static File projectFile;

    public static File getProjectFile() {
        return projectFile;
    }

    public static class ParseFilesTest extends TestCase {
        public ParseFilesTest(String fname) {
            super(fname);
        }
        
        public void testParseFiles() throws IOException, ParserException {
            SourceFileRepository sfr = config.getSourceFileRepository();
        	sfr.getCompilationUnitsFromFiles(
                    new DefaultProjectFileIO(config, getProjectFile()).load());
        }
    }

    public static class SetupModelTest extends TestCase {
        public SetupModelTest(String fname) {
            super(fname);
        }
        
        public void testSetupModel() throws ClassNotFoundException {
            if (!config.getProjectSettings().ensureSystemClassesAreInPath()) {
                throw new ClassNotFoundException("Problem with system setup: Cannot locate system classes");
            }
            config.getChangeHistory().updateModel();
            for (CompilationUnit cu : config.getSourceFileRepository().getCompilationUnits())
            	cu.validateAll();
            new SemanticsChecker(config).checkAllCompilationUnits();
        }
    }

    public static BasicTestsSuite suite() throws IOException, ClassNotFoundException,
    		IllegalAccessException, InstantiationException {
        return new BasicTestsSuite();
    }
    
    public BasicTestsSuite() throws IOException, ClassNotFoundException, IllegalAccessException, InstantiationException {
        this("test/basic/standard.tst", "test/basic/collections.prj");
    }
   
    public BasicTestsSuite(String testConfig, String projectConfig) throws IOException, ClassNotFoundException,
            IllegalAccessException, InstantiationException {
        config = new CrossReferenceServiceConfiguration();
        // should use a specialized error handler instead
        // to check if errors are reported correctly
        config.getProjectSettings().setErrorHandler(new DefaultErrorHandler(0));
        
        projectFile = new File(projectConfig);
        if (!projectFile.exists()) throw new FileNotFoundException("Project File not found!");

        addTest(new ParseFilesTest("testParseFiles"));
        addTest(new SetupModelTest("testSetupModel"));
        BufferedReader reader = new BufferedReader(new FileReader(testConfig));
        String line;
        while ((line = reader.readLine()) != null) {
            line = line.trim();
            if (line.length() > 0 && !line.startsWith("#")) {
                Class<? extends TestCase> c = (Class<? extends TestCase>) Class.forName(line);
                if (!Test.class.isAssignableFrom(c)) {
                    throw new IllegalArgumentException("Class to load is no TestCase");
                }
                addTestSuite(c);
            }
            // should parse arguments and pass them as String arguments?
        }
        reader.close();
    }

    public static void main(String[] args) throws ClassNotFoundException, InstantiationException,
            IllegalAccessException, IOException {
        BasicTestsSuite suite = new BasicTestsSuite("test/basic/standard.tst", "test/basic/collections.prj");
        TestResult result = new TestResult();
        suite.run(result);
        System.out.println("Number of errors: " + result.errorCount() + " / " + result.runCount());
        System.out.println("Number of failures: " + result.failureCount() + " / " + result.runCount());
    }
}
