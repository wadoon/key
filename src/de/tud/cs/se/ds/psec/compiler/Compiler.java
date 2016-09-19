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
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public class Compiler {
    private static final int CLASS_VERSION = 52;
    private static final Logger logger = LogManager.getFormatterLogger();

    private KeYEnvironment<DefaultUserInterfaceControl> environment;
    private File javaFile;
    private boolean debug = false;

    /**
     * TODO
     * 
     * @param javaFile
     * @param debug 
     * @throws ProblemLoaderException
     */
    public Compiler(File javaFile, boolean debug) throws ProblemLoaderException {
        this.javaFile = javaFile;
        this.debug = debug;

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
                SymbolicExecutionJavaProfile.getDefaultInstance(),
                javaFile, // location
                null,     // class path
                null,     // boot class path
                null,     // includes
                true);    // forceNewProfileOfNewProofs
        // @formatter:on
        logger.trace("Built up environment.");
    }

    /**
     * TODO
     * 
     * @return
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
     * TODO
     *
     * @param typeDecl
     * @return
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
     * TODO
     * 
     * @param t
     * @return
     */
    private JavaTypeCompilationResult compile(TypeDeclaration typeDecl) {
        ClassWriter cw = new ClassWriter(
                ClassWriter.COMPUTE_MAXS + ClassWriter.COMPUTE_FRAMES);

        String extending = InformationExtraction.getExtending(typeDecl);
        String[] implementing = InformationExtraction.getImplementing(typeDecl);
        String internalName = InformationExtraction
                .toInternalName(typeDecl.getFullName());

        try {
            
            cw.visit(CLASS_VERSION, InformationExtraction.createOpcode(typeDecl),
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
                CheckClassAdapter.verify(new ClassReader(cw.toByteArray()), false, new PrintWriter(sw));
                
                if (sw.toString().length() != 0) {
                    logger.error("Bytecode failed verification:");
                    logger.error(sw);
                }
            } else {
                logger.error("Compilation failed. This is probably due to an error in one of "
                        + "the translation methods. Run with argument --debug "
                        + "to obtain additional information.");
            }
            
        }

        return new JavaTypeCompilationResult(cw.toByteArray(), internalName);
    }

    /**
     * TODO
     *
     * @param cw
     * @param mDecl
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

            //TODO Remove test code after no longer needed
            //@formatter:off
            try {
                builder.getProof().saveToFile(
                        new File(mDecl.getContainerType().getFullName()
                                + "::" + mDecl.getName() + ".proof"));
            } catch (java.io.IOException e) {
                e.printStackTrace();
            }
            //@formatter:on
        }
        
        mv.visitMaxs(-1, -1);
        mv.visitEnd();
    }

    /**
     * TODO
     *
     * @param cw
     * @param f
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
}
