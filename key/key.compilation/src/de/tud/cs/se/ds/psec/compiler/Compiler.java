package de.tud.cs.se.ds.psec.compiler;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Collectors;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableArray;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.util.CheckClassAdapter;

import de.tud.cs.se.ds.psec.parser.TranslationTacletParser;
import de.tud.cs.se.ds.psec.parser.TranslationTacletParserFE;
import de.tud.cs.se.ds.psec.parser.ast.TranslationDefinitions;
import de.tud.cs.se.ds.psec.parser.exceptions.TranslationTacletInputException;
import de.tud.cs.se.ds.psec.se.SymbolicExecutionInterface;
import de.tud.cs.se.ds.psec.util.InformationExtraction;
import de.tud.cs.se.ds.psec.util.ResourceManager;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaCompilationProfile;

/**
 * The main compiler class. Run {@link #compile()} to initiate compilation.
 *
 * @author Dominic Scheurer
 */
public class Compiler {
    private static final int CLASS_VERSION = 52;
    private static final String TRANSLATION_RULES_PATH = "/de/tud/cs/se/ds/psec/compiler/rules/javaTranslationRules.cmp";
    private static final Logger logger = LogManager.getFormatterLogger();

    private KeYEnvironment<DefaultUserInterfaceControl> environment;
    private File javaFile;
    private String outputDir;
    private boolean debug = false;
    private boolean dumpSET = false;
    private TranslationDefinitions definitions;

    /**
     * Creates a new Compiler object for the given Java type. Be aware that each
     * method to be compiled must have at least a stubby JML specification. This
     * constructor will already start loading all information in the file into
     * KeY; symbolic execution is only started after running {@link #compile()}.
     * 
     * @param javaFile
     *            The file to compile (will compile all contained classes, and
     *            all contained methods with a JML specification).
     * @param outputDir
     *            TODO
     * @param debug
     *            Set to true to display further debug output in case of a
     *            bytecode verification error.
     * @param dumpSET
     *            Set to true to save a .proof file to disk for each compiled
     *            method.
     * @param bailAtParseError
     *            Set to true if the parsing process should stop and not try to
     *            recover in case of a syntax error in the parsed file.
     * @throws ProblemLoaderException
     *             In case an exception occurred while loading the file into
     *             KeY.
     * @throws IOException
     *             If there is an I/O problem while loading the translation
     *             taclets.
     * @throws TranslationTacletInputException
     *             In case that an exception occurred while parsing the
     *             translation taclets.
     */
    public Compiler(File javaFile, String outputDir, boolean debug,
            boolean dumpSET, boolean bailAtParseError)
            throws ProblemLoaderException, TranslationTacletInputException,
            IOException {
        this.javaFile = javaFile;
        this.outputDir = outputDir;
        this.debug = debug;
        this.dumpSET = dumpSET;

        logger.trace("Loading translation definitions...");
        URL url = ResourceManager.instance().getResourceFile(
                TranslationTacletParser.class, TRANSLATION_RULES_PATH);
        definitions = new TranslationTacletParserFE(bailAtParseError)
                .parse(url);

        if (!ProofSettings.isChoiceSettingInitialised()) {
            // Ensure that Taclets are parsed
            logger.trace("Loading taclets...");
            KeYEnvironment<?> env = KeYEnvironment.load(javaFile, null, null,
                    null);
            env.dispose();
            logger.trace("Taclets loaded.");
        }

        logger.trace("Building KeY environment for file %s", javaFile);
        // @formatter:off
        environment = KeYEnvironment.load(
                SymbolicExecutionJavaCompilationProfile.getDefaultInstance(),
                javaFile, // location
                null,     // class path
                null,     // boot class path
                null,     // includes
                true);    // forceNewProfileOfNewProofs
        // @formatter:on
        logger.trace("Built up environment.");
    }

    /**
     * Compiles the supplied Java file and writes it to disk.
     * 
     * @return A {@link List} of {@link JavaTypeCompilationResult}s, one for
     *         each contained class.
     */
    public List<JavaTypeCompilationResult> compile() {
        logger.info("Compiling Java file %s", javaFile);

        List<KeYJavaType> declaredTypes = InformationExtraction
                .getDeclaredTypes(environment);

        assert declaredTypes
                .size() > 0 : "Unexpectedly, no type is declared in the supplied Java file.";

        List<JavaTypeCompilationResult> result = declaredTypes.stream()
                .map(t -> compile(t.getJavaType()))
                .collect(Collectors.toList());

        result.forEach(compilationResult -> {
            Path path = Paths.get(outputDir
                    + compilationResult.getInternalTypeName() + ".class");
            try {
                Files.createDirectories(path.getParent());
                Files.write(path, compilationResult.getBytecode());
            } catch (IOException e) {
                logger.error(
                        "I/O exception in writing compiled file to disk, message:\n%s",
                        e.getMessage());
            }
        });

        logger.info("Finished compilation of Java file %s", javaFile);

        return result;
    }

    /**
     * Compiles the given {@link Type}. This method is only a bridge to
     * {@link #compile(TypeDeclaration)}.
     *
     * @param typeDecl
     *            The {@link Type} to compile.
     * @return A {@link JavaTypeCompilationResult} for the compilation of the
     *         given {@link Type}.
     */
    private JavaTypeCompilationResult compile(Type typeDecl) {
        logger.debug("Compiling type %s", typeDecl.getFullName());

        if (typeDecl instanceof ClassDeclaration
                || typeDecl instanceof InterfaceDeclaration) {
            return compile((TypeDeclaration) typeDecl);
        } else {
            throw new UnsupportedOperationException(
                    "Unexpected top level type: " + typeDecl.getFullName());
        }
    }

    /**
     * Compiles the given {@link TypeDeclaration}. Writes basic information like
     * class version, name etc., and delegates the compilation of
     * {@link FieldDeclaration}s to
     * {@link #compile(ClassWriter, FieldDeclaration)} and to
     * {@link #compile(ClassWriter, ProgramMethod)} for {@link ProgramMethod}s.
     * 
     * @param typeDecl
     *            The {@link TypeDeclaration} to compile.
     * @return A {@link JavaTypeCompilationResult} for the given
     *         {@link TypeDeclaration}.
     */
    private JavaTypeCompilationResult compile(TypeDeclaration typeDecl) {
        ClassWriter cw = new ClassWriter(
                ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES);

        String extending = InformationExtraction.getExtending(typeDecl);
        String[] implementing = InformationExtraction.getImplementing(typeDecl);
        String internalName = InformationExtraction
                .toInternalName(typeDecl.getFullName());

        try {

            cw.visit(CLASS_VERSION,
                    InformationExtraction.createOpcode(typeDecl), internalName,
                    null, extending, implementing);

            ImmutableArray<MemberDeclaration> members = typeDecl.getMembers();
            members.forEach(m -> {
                if (m.getClass().equals(FieldDeclaration.class)) {
                    compile(cw, (FieldDeclaration) m);
                } else if (m.getClass().equals(ProgramMethod.class)
                        && !((ProgramMethod) m).getName().endsWith(">")) {
                    compile(cw, (ProgramMethod) m);
                } else {
                    // TODO: Throw exception
                }
            });

            cw.visitEnd();

        } catch (RuntimeException e) {

            if (debug) {
                logger.error("%s, message: %s", e.getClass().getName(),
                        e.getMessage());

                // DEBUG CODE.
                StringWriter sw = new StringWriter();
                CheckClassAdapter.verify(new ClassReader(cw.toByteArray()),
                        false, new PrintWriter(sw));

                if (sw.toString().length() != 0) {
                    logger.error("Bytecode failed verification:");
                    logger.error(sw);
                }
            } else {
                logger.error(
                        "Compilation failed. This is probably due to an error in one of "
                                + "the translation methods. Run with argument --debug "
                                + "to obtain additional information.");
            }

        }

        return new JavaTypeCompilationResult(cw.toByteArray(), internalName);
    }

    /**
     * Compiles the given {@link ProgramMethod}. Initiates symbolic execution
     * through the {@link SymbolicExecutionInterface} and invokes compilation of
     * the method's body through {@link MethodBodyCompiler}.
     *
     * @param cw
     *            The {@link ClassWriter} of the container of this
     *            {@link ProgramMethod}.
     * @param mDecl
     *            The {@link ProgramMethod} to compile.
     */
    private void compile(ClassWriter cw, ProgramMethod mDecl) {
        logger.debug("Compiling %s %s::%s",
                mDecl.isConstructor() ? "Constructor" : "method",
                mDecl.getContainerType().getJavaType().getFullName(),
                mDecl.getName());

        int accessFlags = InformationExtraction.createOpcode(mDecl);
        String descriptor = InformationExtraction
                .getMethodTypeDescriptor(mDecl);
        MethodVisitor mv = cw.visitMethod(accessFlags,
                mDecl.isConstructor() ? "<init>" : mDecl.getName(), descriptor,
                null, // Signature (for Generics)
                null // Exceptions (TODO!)
        );

        //@formatter:off
        // The following structure could be used to simplicfy the allocation
        // of new local variables, if other things fail.
//        LocalVariablesSorter sorter = new LocalVariablesSorter(accessFlags,
//                descriptor, mv);
        //@formatter:on

        if (!mDecl.isAbstract()) {
            mv.visitCode();

            logger.trace("Running symbolic execution on method %s::%s",
                    mDecl.getContainerType().getJavaType().getFullName(),
                    mDecl.getName());
            SymbolicExecutionTreeBuilder builder = new SymbolicExecutionInterface(
                    environment, javaFile).execute(mDecl);

            if (dumpSET) {
                try {
                    String proofFileName = proofFileNameForProgramMethod(mDecl);
                    builder.getProof().saveToFile(new File(proofFileName));
                    logger.info("Dumping proof tree to file %s", proofFileName);

                } catch (java.io.IOException e) {
                    e.printStackTrace();
                }
            }

            logger.trace("Translating SET of method %s::%s to bytecode",
                    mDecl.getContainerType().getJavaType().getFullName(),
                    mDecl.getName());
            new MethodBodyCompiler(mv, builder.getProof().getServices(),
                    mDecl.getParameters(), definitions, mDecl.isStatic(),
                    mDecl.isVoid() || mDecl.isConstructor()).compile(builder);
        }

        mv.visitMaxs(-1, -1);
        mv.visitEnd();
    }

    /**
     * Compiles the given {@link FieldDeclaration}.
     *
     * @param cw
     *            The {@link ClassWriter} of the container of this
     *            {@link FieldDeclaration}.
     * @param f
     *            The {@link FieldDeclaration} to compile.
     */
    private void compile(ClassWriter cw, FieldDeclaration f) {
        logger.trace("Compiling field declaration %s", f);

        String fieldName = f.getFieldSpecifications().last().getProgramName();
        fieldName = fieldName.substring(fieldName.lastIndexOf(':') + 1);

        // Check whether field is automatically generated, like
        // "...::<classPrepared>" etc.
        if (!fieldName.endsWith(">")) {
            // TODO: Should we really skip the fields generated by KeY?
            FieldVisitor fv = cw
                    .visitField(InformationExtraction.createOpcode(f),
                            fieldName,
                            InformationExtraction.typeToTypeDescriptor(
                                    f.getTypeReference().getKeYJavaType()),
                            null, null);
            fv.visitEnd();
        }
    }

    /**
     * Generates the name for the dumped SET .proof file of the given
     * {@link ProgramMethod}.
     *
     * @param mDecl
     *            The {@link ProgramMethod} the SET of which should be dumped.
     * @return A file name for the .proof file containing the SET of the
     *         {@link ProgramMethod}.
     */
    private String proofFileNameForProgramMethod(ProgramMethod mDecl) {
        return outputDir + mDecl.getContainerType().getFullName() + "::"
                + mDecl.getName() + ".proof";
    }
}
