package de.tud.cs.se.ds.psec.compiler;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
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

import de.tud.cs.se.ds.psec.se.SymbolicExecutionInterface;
import de.tud.cs.se.ds.psec.util.InformationExtraction;
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
    private static final Logger logger = LogManager.getFormatterLogger();

    private KeYEnvironment<DefaultUserInterfaceControl> environment;
    private File javaFile;
    private boolean debug = false;
    private boolean dumpSET = false;

    /**
     * Creates a new Compiler object for the given Java type. Be aware that each
     * method to be compiled must have at least a stubby JML specification. This
     * constructor will already start loading all information in the file into
     * KeY; symbolic execution is only started after running {@link #compile()}.
     * 
     * @param javaFile
     *            The file to compile (will compile all contained classes, and
     *            all contained methods with a JML specification).
     * @param debug
     *            Set to true to display further debug output in case of a
     *            bytecode verification error.
     * @param dumpSET
     *            Set to true to save a .proof file to disk for each compiled
     *            method.
     * @throws ProblemLoaderException
     *             In case an exception occurred while loading the file into
     *             KeY.
     */
    public Compiler(File javaFile, boolean debug, boolean dumpSET)
            throws ProblemLoaderException {
        this.javaFile = javaFile;
        this.debug = debug;
        this.dumpSET = dumpSET;

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
     * Starts compiling the given file.
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
                    InformationExtraction.createOpcode(typeDecl),
                    internalName, null,
                    extending, implementing);

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
        logger.debug("Compiling method %s::%s",
                mDecl.getContainerType().getJavaType().getFullName(),
                mDecl.getName());

        MethodVisitor mv = cw.visitMethod(
                InformationExtraction.createOpcode(mDecl), mDecl.getName(),
                InformationExtraction.getMethodTypeDescriptor(mDecl), null,
                null);

        if (!mDecl.isAbstract()) {
            mv.visitCode();

            logger.trace("Running symbolic execution on method %s::%s",
                    mDecl.getContainerType().getJavaType().getFullName(),
                    mDecl.getName());
            SymbolicExecutionTreeBuilder builder = new SymbolicExecutionInterface(
                    environment, javaFile).execute(mDecl);

            logger.trace("Translating SET of method %s::%s to bytecode",
                    mDecl.getContainerType().getJavaType().getFullName(),
                    mDecl.getName());
            new MethodBodyCompiler(mv, mDecl.getParameters(), mDecl.isStatic())
                    .compile(builder);

            if (dumpSET) {
                try {
                    builder.getProof().saveToFile(
                            new File(proofFileNameForProgramMethod(mDecl)));
                } catch (java.io.IOException e) {
                    e.printStackTrace();
                }
            }
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
            FieldVisitor fv = cw.visitField(
                    InformationExtraction.createOpcode(f), fieldName,
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
    private static String proofFileNameForProgramMethod(ProgramMethod mDecl) {
        return mDecl.getContainerType().getFullName()
                + "::" + mDecl.getName() + ".proof";
    }
}
