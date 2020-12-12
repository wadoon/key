package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.TestGenerationSettings;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;
import de.uka.ilkd.key.smt.testgen.TestGenerationLog;
import de.uka.ilkd.key.testgen.oracle.OracleGenerator;
import de.uka.ilkd.key.testgen.oracle.OracleMethod;
import de.uka.ilkd.key.testgen.oracle.OracleMethodCall;
import de.uka.ilkd.key.util.KeYConstants;
import org.key_project.util.java.StringUtil;

import java.io.*;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * @author gladisch
 * @author herda
 */
public class TestCaseGenerator {
    /**
     * The Java source file extension with a leading dot.
     */
    public static final String JAVA_FILE_EXTENSION_WITH_DOT = ".java";

    /**
     * Constant for the line break which is used by the operating system.
     * <p>
     * <b>Do not use {@code \n}!</b>
     */
    public static final String NEW_LINE = StringUtil.NEW_LINE;

    private static final String NULLABLE = "/*@ nullable */";
    public static final String ALL_OBJECTS = "allObjects";
    public static final String ALL_INTS = "allInts";
    public static final String ALL_BOOLS = "allBools";
    public static final String ALL_HEAPS = "allHeaps";
    public static final String ALL_FIELDS = "allFields";
    public static final String ALL_SEQ = "allSeq";
    public static final String ALL_LOCSETS = "allLocSets";

    public static final String OBJENESIS_NAME = "objenesis-2.2.jar";

    public static final String OLDMap = "old";

    public static final String TAB = "   ";


    static AtomicInteger fileCounter = new AtomicInteger();

    private final boolean junitFormat;
    private static final String DONT_COPY = "aux"; // Classes of the Java
    // environment needed by KeY
    // can be placed in this
    // subdirectory.

    public static boolean modelIsOK(Model m) {
        return m != null && !m.isEmpty() && m.getHeaps() != null
                && !m.getHeaps().isEmpty() && m.getTypes() != null;
    }

    private final Services services;
    private final boolean rflAsInternalClass;
    protected boolean useRFL;
    protected ReflectionClassCreator rflCreator;
    private final String dontCopy;
    protected final String modDir;
    protected final String directory;
    private TestGenerationLog logger;
    private String fileName;
    private String packageName;
    private final String MUTName;
    private final ProofInfo info;
    private final OracleGenerator oracleGenerator;
    private List<OracleMethod> oracleMethods;
    private String oracleMethodCall;
    private final Map<Sort, StringBuilder> sortDummyClass;
    final String dummyPostfix = "DummyImpl";

    // TODO: in future remove this string and provide the file in the
    // KeY-project
    private String compileWithOpenJML = "#!/bin/bash" + NEW_LINE + NEW_LINE
            + "if [ -e \"openjml.jar\" ]" + NEW_LINE
            + "then" + NEW_LINE
            + "   java -jar openjml.jar -cp \".\" -rac *" + JAVA_FILE_EXTENSION_WITH_DOT + NEW_LINE
            + "else" + NEW_LINE
            + "   echo \"openjml.jar not found!\"" + NEW_LINE
            + "   echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"" + NEW_LINE
            + "   echo \"Copy openjml.jar into the directory with test files.\"" + NEW_LINE
            + "fi" + NEW_LINE;

    private String createCompileWithOpenJML(String openJMLPath, String objenesisPath) {
        return "#!/bin/bash" + NEW_LINE + NEW_LINE
                + "if [ -e \"" + openJMLPath + File.separator + "openjml.jar\" ] " + NEW_LINE
                + "then" + NEW_LINE
                + "   if [ -e \"" + objenesisPath + File.separator + OBJENESIS_NAME + "\" ]" + NEW_LINE
                + "   then" + NEW_LINE
                + "      java -jar " + openJMLPath + File.separator + "openjml.jar -cp \"." + objenesisPath + File.separator + OBJENESIS_NAME + "\" -rac *" + JAVA_FILE_EXTENSION_WITH_DOT + NEW_LINE
                + "   else" + NEW_LINE
                + "      echo \"objenesis-2.2.jar not found!\"" + NEW_LINE
                + "   fi" + NEW_LINE
                + "else" + NEW_LINE
                + "   echo \"openjml.jar not found!\"" + NEW_LINE

                + "   echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"" + NEW_LINE
                + "   echo \"Copy openjml.jar into the directory with test files.\"" + NEW_LINE
                + "fi" + NEW_LINE;
    }

    // TODO: in future remove this string and provide the file in the
    // KeY-project
    private final String executeWithOpenJML;

    private String createExecuteWithOpenJML(String path, String objenesisPath) {
        return "#!/bin/bash" + NEW_LINE
                + "if [ -e \"" + path + File.separator + "jmlruntime.jar\" ]" + NEW_LINE
                + "then"
                + "  if [ -e \"" + path + File.separator + "jmlspecs.jar\" ]" + NEW_LINE
                + "  then" + NEW_LINE
                + "     if [ -e \"" + objenesisPath + File.separator + OBJENESIS_NAME + "\" ]" + NEW_LINE
                + "     then" + NEW_LINE
                + "        if [ \"$1\" = \"\" ] ; then" + NEW_LINE
                + "           echo \"Provide the test driver as an argument (without " + JAVA_FILE_EXTENSION_WITH_DOT + " postfix). For example:\"" + NEW_LINE
                + "           echo \"  executeWithOpenJML.sh TestGeneric0 \"" + NEW_LINE
                + "           echo \"Make sure that jmlruntime.jar and jmlspecs.jar are in the\"" + NEW_LINE
                + "           echo \"current directory.\"" + NEW_LINE
                + "           quit" + NEW_LINE
                + "        else" + NEW_LINE
                + "           java -cp " + objenesisPath + File.separator + OBJENESIS_NAME + ":" + path + File.separator + "jmlruntime.jar:" + path + File.separator + "jmlspecs.jar:. $1" + NEW_LINE
                + "        fi" + NEW_LINE
                + "      else" + NEW_LINE
                + "         echo \"objenesis-2.2.jar not found!\"" + NEW_LINE
                + "      fi" + NEW_LINE
                + "else" + NEW_LINE
                + "  echo \"jmlspecs.jar not found!\"" + NEW_LINE
                + "  echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"" + NEW_LINE
                + "  echo \"Copy jmlspecs.jar into the directory with test files.\"" + NEW_LINE
                + "  quit" + NEW_LINE
                + "fi" + NEW_LINE
                + "else" + NEW_LINE
                + "   echo \"jmlruntime.jar not found!\"" + NEW_LINE
                + "   echo \"Download openJML from http://sourceforge.net/projects/jmlspecs/files/\"" + NEW_LINE
                + "   echo \"Copy jmlruntime.jar into the directory with test files.\"" + NEW_LINE
                + "   quit" + NEW_LINE
                + "fi" + NEW_LINE;
    }

    public TestCaseGenerator(Proof proof) {
        this(proof, false);
    }

    public TestCaseGenerator(Proof proof, boolean rflAsInternalClass) {
        super();
        this.rflAsInternalClass = rflAsInternalClass;
        final TestGenerationSettings settings = ProofIndependentSettings.DEFAULT_INSTANCE
                .getTestGenerationSettings();
        services = proof.getServices();
        junitFormat = settings.useJunit();
        useRFL = settings.useRFL();
        modDir = computeProjectSubPath(services.getJavaModel().getModelDir());
        dontCopy = modDir + File.separator + TestCaseGenerator.DONT_COPY;
        directory = settings.getOutputFolderPath();
        sortDummyClass = new HashMap<>();
        info = new ProofInfo(proof);
        MUTName = info.getMUT().getFullName();
        rflCreator = new ReflectionClassCreator();
        executeWithOpenJML = createExecuteWithOpenJML(settings.getOpenjmlPath(), settings.getObjenesisPath());
        compileWithOpenJML = createCompileWithOpenJML(settings.getOpenjmlPath(), settings.getObjenesisPath());
        oracleGenerator = new OracleGenerator(services, rflCreator, useRFL);
        if (junitFormat) {
            oracleMethods = new LinkedList<>();
            oracleMethodCall = getOracleAssertion(oracleMethods);
        }
    }

    /**
     * Computes the project specific sub path of the output directory
     * ({@link #directory}) in which the generated files will be stored.
     *
     * @param modelDir The path to the source files of the performed {@link Proof}.
     * @return The computed sub path.
     */
    protected String computeProjectSubPath(String modelDir) {
        if (modelDir.startsWith("/")) {
            return modelDir;
        } else {
            int index = modelDir.indexOf(File.separator);
            if (index >= 0) {
                return modelDir.substring(index); // Remove drive letter, e.g. Microsoft Windows
            } else {
                return modelDir;
            }
        }
    }

    public String getMUTCall() {
        IProgramMethod m = info.getMUT();
        String name = m.getFullName();
        StringBuilder params = new StringBuilder();
        for (ParameterDeclaration p : m.getParameters()) {
            for (VariableSpecification v : p.getVariables()) {
                IProgramVariable var = v.getProgramVariable();
                params.append(",").append(var.name());
            }
        }
        if (params.length() > 0) {
            params = new StringBuilder(params.substring(1));
        }

        String caller;
        if (m.isStatic()) {
            caller = info.getTypeOfClassUnderTest().getName();
        } else {
            caller = "self";
        }

        if (m.getReturnType().equals(KeYJavaType.VOID_TYPE)) {
            return caller + "." + name + "(" + params + ");";
        } else {
            String returnType = m.getReturnType().getFullName();
            return returnType + " result = " + caller + "." + name + "(" + params + ");";
        }
    }

    protected String buildDummyClassForAbstractSort(Sort sort) {
        final JavaInfo jinfo = services.getJavaInfo();
        final KeYJavaType kjt = jinfo.getKeYJavaType(sort);
        final String className = getDummyClassNameFor(sort);
        if (sortDummyClass.containsKey(sort)) {
            return className;
        }
        final StringBuilder sb = new StringBuilder();
        sortDummyClass.put(sort, sb); // Put the string buffer as soon as
        // possible, due to possible recursive
        // calls of this method.
        sb.append("import ")
                .append(sort.declarationString())
                .append(";")
                .append(NEW_LINE)
                .append(NEW_LINE);
        sb.append("class ")
                .append(className)
                .append(" implements ")
                .append(sort.declarationString())
                .append("{")
                .append(NEW_LINE);

        // TODO:extends or implements depending if it is a class or  interface.
        sb.append(" public ")
                .append(className)
                .append("(){ };")
                .append(NEW_LINE); // default constructor
        for (IProgramMethod m : jinfo.getAllProgramMethods(kjt)) {
            if (m.getFullName().indexOf('<') > -1) {
                continue;
            }
            if (m.isPrivate() || m.isFinal() || !m.isAbstract()) {
                continue;
            }
            sb.append(" ");
            final MethodDeclaration md = m.getMethodDeclaration();
            // sb.append(md.toString() + NEW_LINE);
            if (m.isProtected()) {
                sb.append("protected ");
            }
            if (m.isPublic()) {
                sb.append("public ");
            }
            if (m.isFinal()) {
                sb.append("final "); // Is this possible?
            }
            if (m.isStatic()) {
                sb.append("static ");
            }
            if (m.isSynchronized()) {
                sb.append("synchronized ");
            }
            if (md.getTypeReference() == null) {
                sb.append("void ");
            } else {
                sb.append(md.getTypeReference().toString() + " ");
            }
            sb.append(m.getName() + "(");
            final Iterator<ParameterDeclaration> pdIter = md.getParameters()
                    .iterator();
            int varcount = 0;
            while (pdIter.hasNext()) {
                final ParameterDeclaration pd = pdIter.next();
                if (pd.isFinal()) {
                    sb.append("final ");
                }
                if (pd.getTypeReference() == null) {
                    sb.append("void /*unkown type*/ ");
                } else {
                    sb.append(pd.getTypeReference().toString() + " ");
                }
                if (pd.getVariables().isEmpty()) {
                    sb.append("var" + varcount);
                } else {
                    sb.append(pd.getVariables().iterator().next().getFullName());
                }
                if (pdIter.hasNext()) {
                    sb.append(", ");
                }
                varcount++;
            }
            sb.append(")");
            if (md.getThrown() != null) {
                sb.append(" throws ")
                        .append(md.getThrown().getTypeReferenceAt(0)).append(" ")
                        .append(NEW_LINE).append(" ");
            }
            if (md.getTypeReference() == null) {
                sb.append("{ };");
            } else {
                final String type = md.getTypeReference().toString();
                if (isNumericType(type)) {
                    sb.append("{ return 0;}");
                } else if (type.equals("boolean")) {
                    sb.append("{ return true;}");
                } else if (type.equals("char")) {
                    sb.append("{ return 'a';}");
                } else {
                    boolean returnNull = true;
                    try {
                        final String retType = md.getTypeReference()
                                .getKeYJavaType().getSort().name().toString();
                        if (retType.equals("java.lang.String")) {
                            sb.append("{ return \"" + className + "\";}");
                            returnNull = false;
                        }
                    } catch (final Exception e) {
                        returnNull = true;
                    }
                    if (returnNull) {
                        sb.append("{ return null;}");
                    }
                }
            }
            sb.append(NEW_LINE);
        }
        sb.append("}");
        // System.out.println("--------------------" + NEW_LINE+sb.toString());
        return className;
    }

    private void copyFiles(final String srcName, final String targName)
            throws IOException {
        // We don't want to copy the Folder with API Reference
        // Implementation
        if (srcName.equals(dontCopy)) {
            return;
        }
        // Create the File with given filename and check if it exists and if
        // it's readable
        final File srcFile = new File(srcName);
        if (!srcFile.exists()) {
            throw new IOException("FileCopy: " + "no such source file: "
                    + srcName);
        }
        if (!srcFile.canRead()) {
            throw new IOException("FileCopy: " + "source file is unreadable: "
                    + srcName);
        }
        if (srcFile.isDirectory()) {
            final String newTarget;
            if (srcName.equals(modDir)) {
                newTarget = targName;
            } else {
                newTarget = targName + File.separator + srcFile.getName();
            }
            for (final String subName : srcFile.list()) {
                copyFiles(srcName + File.separator + subName, newTarget);
            }
        } else if (srcFile.isFile()) {
            final File targDir = new File(targName);
            if (!targDir.exists()) {
                targDir.mkdirs();
            }
            final File targFile = new File(targDir, srcFile.getName());
            if (targFile.exists()) {
                if (!targFile.canWrite()) {
                    throw new IOException("FileCopy: "
                            + "destination file is unwriteable: " + targName);
                }
            }
            FileInputStream src = null;
            FileOutputStream targ = null;
            try {
                src = new FileInputStream(srcFile);
                targ = new FileOutputStream(targFile);
                final byte[] buffer = new byte[4096];
                int bytesRead;
                while ((bytesRead = src.read(buffer)) != -1) {
                    targ.write(buffer, 0, bytesRead); // write
                }
            } finally {
                if (src != null) {
                    try {
                        src.close();
                    } catch (final IOException e) {
                    }
                }
                if (targ != null) {
                    try {
                        targ.close();
                    } catch (final IOException e) {
                    }
                }
            }
        } else {
            throw new IOException("FileCopy: " + srcName
                    + " is neither a file nor a directory!");
        }
    }

    protected void createDummyClasses() throws IOException {
        for (final Sort s : sortDummyClass.keySet()) {
            final StringBuilder sb = sortDummyClass.get(s);
            final String file = getDummyClassNameFor(s) + JAVA_FILE_EXTENSION_WITH_DOT;
            writeToFile(file, sb);
        }
    }

    /**
     * Creates the RFL.java file, that provides setter and getter methods using the reflection API
     * as well as object creation functions based on the objenesis library.
     *
     * @throws IOException
     */
    protected void writeRFLFile() throws IOException {
        writeToFile(ReflectionClassCreator.NAME_OF_CLASS + JAVA_FILE_EXTENSION_WITH_DOT, createRFLFileContent());
    }

    /**
     * Used by the Eclipse integration to creat the content of the RFL file.
     *
     * @return The content of the RFL file.
     */
    public StringBuilder createRFLFileContent() {
        return rflCreator.createClass(rflAsInternalClass);
    }

    protected void createOpenJMLShellScript() throws IOException {
        StringBuilder sb = new StringBuilder();
        String filestr = "compileWithOpenJML.sh";
        File file = new File(directory + modDir + File.separator + filestr);
        if (!file.exists()) {
            sb.append(compileWithOpenJML);
            writeToFile(filestr, sb);
        }
        filestr = "executeWithOpenJML.sh";
        file = new File(directory + modDir + File.separator + filestr);
        if (!file.exists()) {
            sb = new StringBuilder();
            sb.append(executeWithOpenJML);
            writeToFile(filestr, sb);
        }
    }

    protected void exportCodeUnderTest() throws IOException {
        // Copy the involved classes without modification
        copyFiles(modDir, directory + modDir);
    }

    private boolean filterVal(String s) {
        return !s.startsWith("#a") && !s.startsWith("#s") && !s.startsWith("#h")
                && !s.startsWith("#l") && !s.startsWith("#f");
    }

    public String generateJUnitTestCase(Model m, Node n) throws IOException {
        fileName = "TestGeneric" + TestCaseGenerator.fileCounter;
        String mut = getMUTCall();
        if (mut == null) {
            mut = "<method under test> //Manually write a call to the method under test, because KeY could not determine it automatically.";
        } else {
            fileName += "_" + MUTName;
        }
        final StringBuilder testCase = new StringBuilder();
        testCase.append(getFilePrefix(fileName, null)).append(NEW_LINE);
        testCase.append(getMainMethod(fileName, 1)).append(NEW_LINE).append(NEW_LINE);
        testCase.append(getTestMethodSignature(0)).append("{").append(NEW_LINE);
        Map<String, Sort> typeInfMap = null;
        if (n != null) {
            typeInfMap = generateTypeInferenceMap(n);
        }
        testCase.append("   //Test preamble: creating objects and intializing test data")
                .append(generateTestCase(m, typeInfMap)).append(NEW_LINE).append(NEW_LINE);
        testCase.append("   //Calling the method under test   ")
                .append(NEW_LINE).append(mut).append(NEW_LINE);
        testCase.append("}").append(NEW_LINE).append("}");
        logger.writeln("Writing test file to:" + directory + modDir
                + File.separator + fileName);
        writeToFile(fileName + JAVA_FILE_EXTENSION_WITH_DOT, testCase);
        exportCodeUnderTest();
        createDummyClasses();
        try {
            if (useRFL) writeRFLFile();
        } catch (Exception ex) {
            logger.writeln("Error: The file RFL" + JAVA_FILE_EXTENSION_WITH_DOT + " is either not generated or it has an error.");
        }
        createOpenJMLShellScript();
        TestCaseGenerator.fileCounter.incrementAndGet();
        return testCase.toString();
    }


    protected String getOracleAssertion(List<OracleMethod> oracleMethods) {
        Term postcondition = getPostCondition();

        OracleMethod oracle = oracleGenerator.generateOracleMethod(postcondition);


        OracleMethodCall oracleCall = new OracleMethodCall(oracle, oracle.getArgs());

        oracleMethods.add(oracle);
        oracleMethods.addAll(oracleGenerator.getOracleMethods());

        return "assertTrue(" + oracleCall.toString() + ");";
    }

    private Term getPostCondition() {
        return info.getPostCondition();
    }

    public String generateJUnitTestSuite(Collection<SMTSolver> problemSolvers) throws IOException {
        initFileName();
        StringBuilder testSuite = createTestCaseCotent(problemSolvers);
        writeToFile(fileName + JAVA_FILE_EXTENSION_WITH_DOT, testSuite);
        logger.writeln("Writing test file to:" + directory + modDir
                + File.separator + fileName + JAVA_FILE_EXTENSION_WITH_DOT);
        exportCodeUnderTest();
        createDummyClasses();
        try {
            if (useRFL) writeRFLFile();
        } catch (Exception ex) {
            logger.writeln("Error: The file RFL" + JAVA_FILE_EXTENSION_WITH_DOT + " is either not generated or it has an error.");
        }
        createOpenJMLShellScript();
        TestCaseGenerator.fileCounter.incrementAndGet();
        return testSuite.toString();
    }

    public void initFileName() {
        fileName = "TestGeneric" + TestCaseGenerator.fileCounter;
        String mut = getMUTCall();
        if (mut == null) {
            mut = "<method under test> //Manually write a call to the method under test, because KeY could not determine it automatically.";
        } else {
            fileName += "_" + MUTName;
        }
    }

    public StringBuilder createTestCaseCotent(Collection<SMTSolver> problemSolvers) {
        // TODO: Include package definition (same as type containing the proof obligation)
        final StringBuilder testSuite = new StringBuilder();
        testSuite.append(getFilePrefix(fileName, packageName) + NEW_LINE);
        final StringBuilder testMethods = new StringBuilder();
        int i = 0;
        for (final SMTSolver solver : problemSolvers) {
            try {
                final StringBuilder testMethod = new StringBuilder();
                final String originalNodeName = solver.getProblem().getGoal()
                        /* Warning this is wrong if we generate a test from an inner node (e.g. closed proof tree),
                           because goals are mutable. A Node should be used here instead. */
                        .proof().name().toString();
                boolean success = false;
                if (solver.getSocket().getQuery() != null) {
                    final Model m = solver.getSocket().getQuery().getModel();
                    if (TestCaseGenerator.modelIsOK(m)) {
                        logger.writeln("Generate: " + originalNodeName);
                        Map<String, Sort> typeInfMap = generateTypeInferenceMap(solver.getProblem().getGoal().node());

                        testMethod.append("  //" + originalNodeName + NEW_LINE);
                        testMethod.append(getTestMethodSignature(i) + "{" + NEW_LINE);
                        testMethod
                                .append("   //Test preamble: creating objects and intializing test data"
                                        + generateTestCase(m, typeInfMap) + NEW_LINE + NEW_LINE);

                        Set<Term> vars = new HashSet<>();
                        info.getProgramVariables(info.getPO(), vars);
                        testMethod.append(TAB + "//Other variables" + NEW_LINE + getRemainingConstants(m.getConstants().keySet(), vars) + NEW_LINE);
                        testMethod
                                .append("   //Calling the method under test   " + NEW_LINE
                                        + info.getCode() + NEW_LINE);


                        if (junitFormat) {
                            testMethod.append("   //calling the test oracle" + NEW_LINE + TAB + oracleMethodCall + NEW_LINE);
                        }

                        testMethod.append(" }" + NEW_LINE + NEW_LINE);
                        i++;
                        success = true;
                        testMethods.append(testMethod);
                    }
                }
                if (!success) {
                    logger.writeln("A model (test data) was not generated for:"
                            + originalNodeName);
                }
            } catch (final Exception ex) {
                for (StackTraceElement ste : ex.getStackTrace()) {
                    logger.writeln(ste.toString());
                }
                logger.writeln("A test case was not generated due to an exception. Continuing test generation...");
            }
        }
        if (i == 0) {
            logger.writeln("Warning: no test case was generated. Adjust the SMT solver settings (e.g. timeout) in Options->SMT Solvers.");
        } else if (i < problemSolvers.size()) {
            logger.writeln("Warning: SMT solver could not solve all test data constraints. Adjust the SMT solver settings (e.g. timeout) in Options->SMT Solvers.");
        }
        testSuite.append(getMainMethod(fileName, i) + NEW_LINE + NEW_LINE);
        testSuite.append(testMethods);

        if (junitFormat) {
            for (OracleMethod m : oracleMethods) {
                testSuite.append(NEW_LINE + NEW_LINE);
                testSuite.append(m);
            }
        }

        if (rflAsInternalClass) {
            testSuite.append(createRFLFileContent());
        }

        testSuite.append(NEW_LINE + "}");
        return testSuite;
    }

    protected String inferSort(Map<String, Sort> typeInfMap, String progVar) {
        if (typeInfMap.containsKey(progVar)) {
            return typeInfMap.get(progVar).name().toString();
        }
        System.out.println("Warning: inferSort did not find:" + progVar);
        return "NOTYPE";
    }

    protected Map<String, Sort> generateTypeInferenceMap(Node n) {
        HashMap<String, Sort> typeInfMap = new HashMap<String, Sort>();
        Iterator<SequentFormula> formIter = n.sequent().iterator();
        //System.out.println("\n---------------------------------------");
        while (formIter.hasNext()) {
            Term t = formIter.next().formula();
            generateTypeInferenceMapHelper(t, typeInfMap);
        }
        return typeInfMap;
    }

    private void generateTypeInferenceMapHelper(Term t, Map<String, Sort> map) {
        Operator op = t.op();
        if (op instanceof ProgramVariable) {
            ProgramVariable pv = (ProgramVariable) t.op();
            final String name = pv.name().toString();
            if (map.containsKey(name)) {
                if (map.get(name) != pv.sort()) {
                    System.out.println("Warning: ProgramVariable " + name + " is ambiguous.");
                }
            } else {
                //System.out.println("PV "+name+"  Sort: "+pv.sort()+ " KeYJavaType: "+pv.getKeYJavaType().toString());
                map.put(name, pv.sort());
            }
        }/*  ObserverFunctions are query methods and ObsFunc java.lang.Object::<inv>
        else if(op instanceof ObserverFunction){
            ObserverFunction func = (ObserverFunction)t.op();
            final String name = func.name().toString();
            if(map.containsKey(name)){
                if(map.get(name)!=func.sort()){
                    System.out.println("ObsFunction "+name+" is AMBIGUOUS.");
                }
            }else{
                System.out.println("ObsFunc "+name+"  KeYJavaType: "+func.getType());                
                map.put(name, func.sort());
            }
        }*/ else if (op instanceof Function && !(op instanceof ObserverFunction)) {
            //This case collects fields of classes. The function itself has 
            // sort "Field" because it is just the name of the field. To get
            // the actual class of the field
            Function func = (Function) t.op();
            String name = func.name().toString();
            Sort sort = func.sort();
            HeapLDT hLDT = services.getTypeConverter().getHeapLDT();
            if (sort == hLDT.getFieldSort()) {
                // String fieldSort = HeapLDT.getClassName(func);
                ProgramVariable pv = getProgramVariable(t);

                if (pv != null) {
                    name = name.replace("::$", "::");

                    if (map.containsKey(name)) {
                        if (map.get(name) != pv.sort()) {
                            System.out.println("Warning: Function " + name + " is ambiguous.");
                        }
                    } else {
                        //System.out.println("Func "+name+"  Sort: "+func.sort()+ " FieldSort:"+fieldSort + "  PV.sort:"+pv.sort());                
                        map.put(name, pv.sort());
                    }
                } else {
                    //TODO:
                    //System.out.println("Program variable could not be determined:"+t.toString());
                }
            }
        }

        for (int i = 0; i < t.arity(); i++) {
            generateTypeInferenceMapHelper(t.sub(i), map);
        }
    }

    private ProgramVariable getProgramVariable(Term locationTerm) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        ProgramVariable result = null;
        if (locationTerm.op() instanceof Function) {
            Function function = (Function) locationTerm.op();
            // Make sure that the function is not an array
            if (heapLDT.getArr() != function) {
                String typeName = HeapLDT.getClassName(function);
                KeYJavaType type = services.getJavaInfo().getKeYJavaType(typeName);
                if (type != null) {
                    String fieldName = HeapLDT.getPrettyFieldName(function);
                    result = services.getJavaInfo().getAttribute(fieldName, type);
                }
            }
        }
        return result;
    }

    private String getRemainingConstants(Collection<String> existingConstants, Collection<Term> newConstants) {
        String result = "";

        for (Term c : newConstants) {

            if (!existingConstants.contains(c.toString())) {

                String init = "null";
                if (c.sort().equals(services.getTypeConverter().getIntegerLDT().targetSort())) {
                    init = "0";
                } else if (c.sort().equals(services.getTypeConverter().getBooleanLDT().targetSort())) {
                    init = "false";
                }

                result += NEW_LINE + TAB + NULLABLE + " " + getSafeType(c.sort()) + " " + c + " = " + init + ";";
                if (junitFormat) {
                    result += NEW_LINE + TAB + NULLABLE + " " + getSafeType(c.sort()) + " " + getPreName(c.toString()) + " = " + init + ";";
                }


            }

        }

        return result;
    }


    private boolean isInPrestate(Collection<? extends ObjectVal> prestate, ObjectVal o) {
        return true;
        //		return prestate.contains(o) && 
        //		        services.getTypeConverter().isReferenceType(
        //		                services.getJavaInfo().getKeYJavaType(o.getSort()).getJavaType());

    }

    private boolean isInPrestate(Collection<? extends ObjectVal> prestate, String name) {
        return true;
        //		// TODO return only needed objects		
        //				for(ObjectVal o : prestate){
        //				    if (services.getTypeConverter().isReferenceType(
        //		                                services.getJavaInfo().getKeYJavaType(o.getSort()).getJavaType())) {
        //					String oName = createObjectName(o);
        //					if(oName.equals(name)){
        //						return true;
        //					}
        //				    }
        //				}
        //				
        //				return false;
    }

    public String generateModifierSetAssertions(Model m) {
        StringBuilder res = new StringBuilder();

        res.append(TAB + "//Modifier set assertions");


        return res.toString();
    }

    public String generateTestCase(Model m, Map<String, Sort> typeInfMap) {
        m.removeUnnecessaryObjects();

        Set<String> objects = new HashSet<String>();

        final List<Assignment> assignments = new LinkedList<Assignment>();
        Heap heap = null;
        for (final Heap h : m.getHeaps()) {
            if (h.getName().equals(HeapLDT.BASE_HEAP_NAME.toString())) {
                heap = h;
                break;
            }
        }

        Set<ObjectVal> prestate = new HashSet<>();
        if (heap != null) {

            // create objects
            for (final ObjectVal o : heap.getObjects()) {
                if (o.getName().equals("#o0")) {
                    continue;
                }
                final String type = getSafeType(o.getSort());
                String right;
                if (type.endsWith("[]")) {
                    right = "new " + type.substring(0, type.length() - 2) + "["
                            + o.getLength() + "]";
                } else if (o.getSort() == null || o.getSort().toString().equals("Null")) {
                    right = "null";
                } else {
                    if (useRFL) {
                        right = "RFL.new" + ReflectionClassCreator.cleanTypeName(type) + "()";
                        rflCreator.addSort(type);
                    } else
                        right = "new " + type + "()";
                }

                String objName = createObjectName(o);
                objects.add(objName);
                assignments.add(new Assignment(type, objName, right));
                if (junitFormat && isInPrestate(prestate, o)) {
                    assignments.add(new Assignment(type, getPreName(objName), right));
                }
            }
        }
        // init constants
        for (final String c : m.getConstants().keySet()) {
            String val = m.getConstants().get(c);
            if (filterVal(val) && !c.equals("null")) {
                boolean isObject = false;
                boolean isLiteral = false;
                String type = "int";
                String declType = "int";
                if (val.equals("true") || val.equals("false")) {
                    type = "boolean";
                    isLiteral = true;
                } else if (StringUtil.isNumber(val)) {
                    isLiteral = true;
                } else if (val.startsWith("#o")) {
                    isObject = true;
                    type = this.inferSort(typeInfMap, c);
                    /*
					final ObjectVal o = getObject(heap, val);
					if (o != null) {
						if (val.equals("#o0")
								&& m.getTypes().getOriginalConstantType(c) != null) {
							type = m.getTypes().getOriginalConstantType(c)
									.name().toString();
						} else {
							type = getSafeType(o.getSort()); //o.getSort().name().toString();
						}
					} else {
						type = "Object";
					}
                     */

                }

                if (!type.equals("NOTYPE")) {
                    if (isObject) {
                        declType = NULLABLE + " " + type;
                    } else {
                        declType = type;
                    }
                    val = translateValueExpression(val);
                    assignments.add(new Assignment(declType, c, "(" + type + ")" + val));
                    if (junitFormat && (isObject || Character.isJavaIdentifierStart(c.charAt(0))) && isInPrestate(prestate, val)) {
                        if (isLiteral) {
                            assignments.add(new Assignment(declType, getPreName(c), "(" + type + ")" + val));
                        } else {
                            assignments.add(new Assignment(declType, getPreName(c), "(" + type + ")" + getPreName(val)));
                        }

                    }
                }
            }
        }
        // init fields
        if (heap != null) {
            for (final ObjectVal o : heap.getObjects()) {
                if (o.getName().equals("#o0") || o.getSort().name().toString().endsWith("Exception")) {
                    continue;
                }
                final String receiverObject = createObjectName(o);
                for (final String f : o.getFieldvalues().keySet()) {
                    if (f.contains("<") || f.contains(">")) {
                        continue;
                    }
                    String fieldName = f.substring(f.lastIndexOf(":") + 1);
                    fieldName = fieldName.replace("|", "");
                    String val = o.getFieldvalues().get(f);
                    String fieldName2 = f.replace("|", "");
                    final String vType = this.inferSort(typeInfMap, fieldName2);
                    rflCreator.addSort(vType); //possible bug if vType represents an abstract type or an interface. See: getSafeType.
                    val = translateValueExpression(val);
                    final String rcObjType = getSafeType(o.getSort());
                    assignments
                            .add(new Assignment(new RefEx(rcObjType, receiverObject, vType, fieldName), "(" + vType + ")" + val));

                    if (junitFormat && isInPrestate(prestate, o)) {
                        //if value that is pointed to is object and in prestate then use prestate object
                        if (!vType.equals("int") && !vType.equals("boolean") && isInPrestate(prestate, val) && !val.equals("null")) {
                            val = getPreName(val);
                        }


                        assignments
                                .add(new Assignment(new RefEx(rcObjType, getPreName(receiverObject), vType, fieldName), "(" + vType + ")" + val));
                    }

                }
                if (o.getSort() != null
                        && o.getSort().name().toString().endsWith("[]")) {

                    String safeType = getSafeType(o.getSort());
                    String elementType = safeType.substring(0, safeType.length() - 2);
                    rflCreator.addSort(safeType);

                    for (int i = 0; i < o.getLength(); i++) {
                        final String fieldName = "[" + i + "]";
                        String val = o.getArrayValue(i);
                        val = translateValueExpression(val);
                        assignments.add(new Assignment(receiverObject + fieldName, val));

                        if (junitFormat && isInPrestate(prestate, o)) {


                            if (!elementType.equals("int") && !elementType.equals("boolean") && isInPrestate(prestate, val) && !val.equals("null")) {
                                val = getPreName(val);
                            }

                            assignments.add(new Assignment(getPreName(receiverObject) + fieldName, val));
                        }


                    }
                }
            }
        }

        final StringBuilder result = new StringBuilder();
        for (final Assignment a : assignments) {
            result.append(NEW_LINE + "   ");
            result.append(a.toString(useRFL));
        }

        if (junitFormat) {
            result.append(NEW_LINE)
                    .append(createOldMap(objects)).append(NEW_LINE)
                    .append(createBoolSet()).append(NEW_LINE)
                    .append(createIntSet()).append(NEW_LINE)
                    .append(createObjSet(heap)).append(NEW_LINE);
        }

        return result.toString();
    }

    private String createOldMap(Set<String> objNames) {
        StringBuilder result = new StringBuilder(
                NEW_LINE + TAB + "Map<Object,Object> " + OLDMap + " = new HashMap<Object,Object>();");
        for (String o : objNames) {
            result.append(NEW_LINE)
                    .append(TAB)
                    .append(OLDMap)
                    .append(".put(")
                    .append(getPreName(o)).append(",")
                    .append(o).append(");");
        }
        return result.toString();
    }

    private String getPreName(String val) {
        return OracleGenerator.PRE_STRING + val;
    }

    private String createObjectName(final ObjectVal o) {
        return o.getName().replace("#", "_");
    }

    private String getDummyClassNameFor(Sort sort) {
        final JavaInfo jinfo = services.getJavaInfo();
        final KeYJavaType kjt = jinfo.getKeYJavaType(sort);
        return kjt.getName() + dummyPostfix;
    }

    private String getFilePrefix(String className, String packageName) {
        String res = "/** This is a test driver generated by KeY " + KeYConstants.VERSION + " (www.key-project.org). " + NEW_LINE +
                " * Possible use cases:" + NEW_LINE +
                " *  Use Case 1. Using JUnit 4:" + NEW_LINE +
                " *        javac -cp .:PATH_TO_JUNIT4_JAR *.java" + NEW_LINE +
                " *        java  -cp .:PATH_TO_JUNIT4_JAR:PATH_TO_HAMCREST_JAR org.junit.runner.JUnitCore " + className + NEW_LINE +
                " *  Use Case 2. Use JML runtime checker: " + NEW_LINE +
                " *      Compile this file and and execute the main method with a JML runtime checker. On linux you can use the built-in scripts:" + NEW_LINE +
                " *        ./compileWithOpenJML.sh" + NEW_LINE +
                " *        ./executeWithOpenJML.sh " + className + NEW_LINE +
                " *  Use Case 3. Use simply a program debugger to follow and understand the execution of the program." + NEW_LINE +
                " * @author Christoph Gladisch" + NEW_LINE +
                " * @author Mihai Herda" + NEW_LINE +
                " */" + NEW_LINE;
        if (packageName != null) {
            res += "package " + packageName + ";" + NEW_LINE;
        }

        if (junitFormat) {
            res += "import java.util.Set;" + NEW_LINE
                    + "import java.util.HashSet;" + NEW_LINE
                    + "import java.util.Map;" + NEW_LINE
                    + "import java.util.HashMap;" + NEW_LINE
                    + " public class " + className
                    + " extends junit.framework.TestCase {" + NEW_LINE + NEW_LINE
                    + " public static junit.framework.Test suite() { "
                    + "   return new junit.framework.JUnit4TestAdapter(" + className + ".class);" + NEW_LINE
                    + " } " + NEW_LINE
                    + NEW_LINE + " public " + className + "(){}" + NEW_LINE + NEW_LINE;
        } else {
            res += "public class " + className + "{ " + NEW_LINE + NEW_LINE + " public "
                    + className + "(){}" + NEW_LINE;
        }
        return res;
    }

    private StringBuilder getMainMethod(String className, int i) {
        final StringBuilder res = new StringBuilder();
        res.append(" public static void  main (java.lang.String[]  arg) {" + NEW_LINE
                + "   " + className + " testSuiteObject;" + NEW_LINE
                + "   testSuiteObject=new " + className + " ();" + NEW_LINE + NEW_LINE);
        for (int j = 0; j < i; j++) {
            res.append("   testSuiteObject.testcode" + j + "();" + NEW_LINE);
        }
        if (i == 0) {
            res.append("   //Warning:no test methods were generated." + NEW_LINE);
        }
        res.append(" }");
        return res;
    }

    private String createBoolSet() {
        StringBuilder res = new StringBuilder();
        //bool
        String allbool = ALL_BOOLS;
        res.append(NEW_LINE);
        res.append(TAB + "Set<Boolean> " + allbool + "= new HashSet<Boolean>();" + NEW_LINE);
        res.append(TAB + allbool + ".add(true);" + NEW_LINE);
        res.append(TAB + allbool + ".add(false);" + NEW_LINE);
        return res.toString();
    }

    private String createIntSet() {

        StringBuilder res = new StringBuilder();
        long size = ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().intBound;

        long low = (long) -Math.pow(2, size - 1);
        long hi = (long) (Math.pow(2, size - 1) - 1);

        String allint = ALL_INTS;
        res.append(TAB + "Set<Integer> " + allint + "= new HashSet<Integer>();" + NEW_LINE);

        for (long i = low; i <= hi; i++) {
            res.append(TAB + allint + ".add(" + i + ");" + NEW_LINE);
        }

        return res.toString();
    }

    private String createObjSet(Heap h) {

        StringBuilder res = new StringBuilder();

        res.append(TAB + "Set<Object> " + ALL_OBJECTS + "= new HashSet<Object>();" + NEW_LINE);

        for (ObjectVal o : h.getObjects()) {
            String name = o.getName();
            if (name.equals("#o0")) {
                continue;
            }
            name = name.replace("#", "_");
            res.append(TAB + ALL_OBJECTS + ".add(" + name + ");" + NEW_LINE);

        }

        return res.toString();
    }


    public String getSafeType(Sort sort) {
        if (sort == null || sort.name().toString().equals("Null")) {
            return "java.lang.Object"; // TODO:Hopefully this is correct
        } else if (sort.isAbstract()) {
            return buildDummyClassForAbstractSort(sort);
        } else {
            return sort.name().toString();
        }
    }

    private String getTestMethodSignature(int i) {
        final String sig = " public void  testcode" + i + "()";
        if (junitFormat) {
            return "@org.junit.Test" + NEW_LINE + sig;
        } else {
            return sig;
        }
    }

    public boolean isJunit() {
        return junitFormat;
    }

    protected boolean isNumericType(String type) {
        return type.equals("byte") || type.equals("short")
                || type.equals("int") || type.equals("long")
                || type.equals("float") || type.equals("double");
    }

    protected boolean isPrimitiveType(String type) {
        return isNumericType(type) || type.equals("boolean")
                || type.equals("char");
    }

    public void setLogger(TestGenerationLog logger) {
        this.logger = logger;
    }

    protected String translateValueExpression(String val) {
        if (val.contains("/")) {
            val = val.substring(0, val.indexOf("/"));
        }
        if (val.equals("#o0")) {
            return "null";
        }
        val = val.replace("|", "");
        val = val.replace("#", "_");
        return val;
    }

    public void writeToFile(String file, StringBuilder sb) throws IOException {
        final File dir = new File(directory + modDir);
        if (!dir.exists()) {
            dir.mkdirs();
        }
        final File pcFile = new File(dir, file);
        System.out.println("Writing file:" + pcFile.toString());
        final BufferedWriter bw = new BufferedWriter(new FileWriter(pcFile));
        try {
            bw.write(sb.toString());
        } finally {
            bw.close();
        }
        // create a temporary file
        // File logFile=new File("TestGeneric"+fileCounter+JAVA_FILE_EXTENSION_WITH_DOT);
        // BufferedWriter writer = new BufferedWriter(new
        // FileWriter(logFile));
        // writer.write (sb.toString());
        // Close writer
        // writer.close();
    }

    public boolean isUseRFL() {
        return useRFL;
    }

    public String getFileName() {
        return fileName;
    }

    public void setFileName(String fileName) {
        this.fileName = fileName;
    }

    public String getPackageName() {
        return packageName;
    }

    public void setPackageName(String packageName) {
        this.packageName = packageName;
    }

    public boolean isRflAsInternalClass() {
        return rflAsInternalClass;
    }
}
