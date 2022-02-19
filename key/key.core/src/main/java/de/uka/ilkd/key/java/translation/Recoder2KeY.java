// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.translation;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.ast.type.VoidType;
import com.github.javaparser.ast.visitor.VoidVisitor;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.MethodUsage;
import de.uka.ilkd.key.Services;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.api.JavaService;
import de.uka.ilkd.key.java.ast.CompilationUnit;
import de.uka.ilkd.key.java.ast.ModelElement;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.transformations.KeyJavaPipeline;
import de.uka.ilkd.key.java.transformations.pipeline.TransformationPipelineServices;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Collectors;

/**
 * This class is the bridge between recoder ast data structures and KeY data
 * structures. Syntactical entities and types can be transferred from recoder to
 * KeY.
 * <p>
 * It manages the entire contact with the recoder framework and ensures that
 * their cross-referencing data is always uptodate. Prior to reading any source
 * code, special classes (i.e. stubs for some needed library classes) are parsed
 * in to have them available at any time.
 * <p>
 * To use a Recoder2KeY bridge to convert data structures you can use the
 * functions: {@link #readCompilationUnit(String)},
 * {@link #readCompilationUnitsAsFiles(String[], FileRepo)} or the
 * {@link #readBlock(String, Context)}-methods.
 * <p>
 * Results are often stored in caches.
 * <p>
 * It used to be monolithic but now uses separate classes for doing the actual
 * conversion and type conversion.
 */

public class Recoder2KeY implements JavaReader {

    /**
     * counter used to enumerate the anonymous implicit classes
     */
    private static AtomicInteger interactCounter = new AtomicInteger();

    /**
     *
     */
    private final Services services;

    /**
     *
     */
    private final JavaService javaService;

    /**
     * the set of File objects that describes the classpath to be searched
     * for classes.
     * it may contain a null file which indicates that the default classes are
     * not to be read.
     */
    @Nonnull
    private List<File> classPath;

    /**
     * the File object that describes the directory from which the internal
     * classes are to be read. They are read in differently - therefore the
     * second category. A null value indicates that the boot classes are to
     * be read from an internal repository.
     */
    @Nullable
    private File bootClassPath;

    /**
     * this flag indicates whether we are currently parsing library classes
     * (special classes)
     */
    private boolean parsingLibs = false;

    /**
     * the object that handles the transformation from recoder types to KeY
     * types
     */
    private final Recoder2KeYTypeConverter typeConverter;

    /**
     * the list of classnames that contain the classes that are referenced but not
     * defined. For those classe types a dummy stub is created at parse time.
     */
    private Collection<? extends CompilationUnit> dynamicallyCreatedCompilationUnits;
    private Map<ProgramElement, Node> mapping = new IdentityHashMap<>();


    /**
     * create a new Recoder2KeY transformation object.
     * <p>
     * The converter and type converter associated with this object will be
     * created. Several properties of the recoder framework will be set up.
     * <p>
     * The classpath is set to null, the mapping is retrieved from the services,
     * as well as the underlying type converter
     *
     * @param nss the namespaces to work upon, not null
     * @param bcp
     * @param cp
     */
    public Recoder2KeY(Services services, JavaService javaService, NamespaceSet nss,
                       TypeConverter typeConverter, File bcp, List<File> cp) {
        this.services = services;
        this.javaService = javaService;
        this.typeConverter = new Recoder2KeYTypeConverter(services, typeConverter, nss, this);
        this.bootClassPath = bcp;
        this.classPath = new ArrayList<>(cp);
    }

    /**
     * create a new Recoder2KeY transformation object.
     * <p>
     * The converter and type converter associated with this object will be
     * created. Several properties of the recoder framework will be set up.
     * <p>
     * The classpath is set to null, the mapping is retrieved from the services,
     * as well as the underlying type converter
     *
     * @param services services to retrieve objects from, not null
     * @param nss      the namespaces to work upon, not null
     */
    public Recoder2KeY(Services services, NamespaceSet nss) {
        this(services, services.getJavaService(), nss, services.getTypeConverter(), null, Collections.emptyList());
    }

    /**
     * create a new Recoder2KeY transformation object.
     * <p>
     * The converter and type converter associated with this object will be
     * created. Several properties of the recoder framework will be set up.
     *
     * @param classPath the classpath to look up source files, ignored if null
     * @param nss       the namespaces to work upon, not null
     * @param tc        the type converter, not null
     * @throws IllegalArgumentException if arguments are not valid (null e.g.)
     */
    private Recoder2KeY(Services services, String classPath, NamespaceSet nss, TypeConverter tc) {
        this(services, services.getJavaService(), nss, tc, null, Collections.singletonList(new File(classPath)));
    }

    /**
     * reduce the size of a string to a maximum of 150 characters. Introduces
     * ellipses [...]
     */
    private static String trim(String s) {
        return trim(s, 150);
    }

    /**
     * reduce the size of a string to a maximum of length.
     */
    private static String trim(String s, int length) {
        if (s.length() > length)
            return s.substring(0, length - 5) + "[...]";
        return s;
    }

    /**
     * tries to parse recoders exception position information
     */
    private static int[] extractPositionInfo(String errorMessage) {
        if (errorMessage == null || errorMessage.indexOf('@') == -1) {
            return new int[0];
        }
        int line = -1;
        int column = -1;
        try {
            String pos = errorMessage.substring(errorMessage.indexOf("@") + 1);
            pos = pos.substring(0, pos.indexOf(" "));
            line = Integer.parseInt(pos.substring(0, pos.indexOf('/')));
            column = Integer.parseInt(pos.substring(pos.indexOf('/') + 1));
        } catch (NumberFormatException nfe) {
            Debug.out("recoder2key:unresolved reference at " + "line:" + line + " column:" + column);
            return new int[0];
        } catch (StringIndexOutOfBoundsException siexc) {
            return new int[0];
        }
        return new int[]{line, column};
    }

    /**
     * report an error in form of a ConvertException. The cause is always
     * attached to the resulting exception.
     *
     * @param message message to be used.
     * @param t       the cause of the exceptional case
     * @throws ConvertException always
     */
    public static void reportError(String message, Throwable t) {
        // Attention: this highly depends on Recoders exception messages!
        Throwable cause = t;
        if (t instanceof ExceptionHandlerException) {
            if (t.getCause() != null) {
                cause = t.getCause();
            }
        }

        if (cause instanceof PosConvertException) {
            throw (PosConvertException) cause;
        }

        int[] pos = extractPositionInfo(cause.toString());
        final RuntimeException rte;
        if (pos.length > 0) {
            rte = new PosConvertException(message, pos[0], pos[1]);
            rte.initCause(cause);
        } else {
            rte = new ConvertException(message, cause);
        }

        throw rte;
    }

    /**
     * return the associated type converter object
     *
     * @return not null
     */
    public Recoder2KeYTypeConverter getTypeConverter() {
        return typeConverter;
    }

    /**
     * are we currently parsing library code (special classes)?
     *
     * @return true iff currently parsing special classes.
     */
    public boolean isParsingLibs() {
        return parsingLibs;
    }

    // ----- parsing of compilation units

    /**
     * set this to true before parsing special classes and to false afterwards.
     *
     * @param v the state of the special parsing flage
     */
    private void setParsingLibs(boolean v) {
        parsingLibs = v;
    }


    /**
     * parse a list of java files and transform it to the corresponding KeY
     * entities.
     * <p>
     * Each element of the array is treated as a filename to read in.
     *
     * @param filenames a list of strings, each element is interpreted as a file to be
     *                  read. not null.
     * @param fileRepo  the fileRepo which will store the files
     * @return a new list containing the recoder compilation units corresponding
     * to the given files.
     * @throws ParseExceptionInFile any exception occurring while treating the file is wrapped
     *                              into a parse exception that contains the filename.
     */
    public CompilationUnit[] readCompilationUnitsAsFiles(String[] filenames, FileRepo fileRepo) {
        var cUnits = readCompilationUnitsAsFilesBare(filenames, fileRepo);
        CompilationUnit[] result = new CompilationUnit[cUnits.size()];
        for (int i = 0, sz = cUnits.size(); i < sz; i++) {
            Debug.out("converting now " + filenames[i]);
            try {
                var cu = cUnits.get(i);
                result[i] = (CompilationUnit) convert2Key(cu);
            } catch (Exception e) {
                throw new ParseExceptionInFile(filenames[i], e);
            }
        }
        return result;
    }

    /**
     * @param n
     * @return
     */
    protected ProgramElement convert2Key(com.github.javaparser.ast.Node n) {
        var visitor = createTranslationVisitor();
        return n.accept(visitor, null);
    }

    /**
     * @return
     */
    protected JavaParser2Key createTranslationVisitor() {
        return new JavaParser2Key(mapping);
    }

    /**
     * Helper method for parsing a single compilation unit when a FileRepo is present.
     *
     * @param fileRepo the FileRepo that provides the InputStream
     * @param filename the name of the file to read
     * @return the parsed compilation unit
     * @throws ParseExceptionInFile exceptions are wrapped into this to provide location information
     */
    private ParseResult<com.github.javaparser.ast.CompilationUnit> readViaFileRepo(FileRepo fileRepo, String filename)
            throws ParseExceptionInFile {
        try (InputStream is = fileRepo.getInputStream(Paths.get(filename));
             Reader fr = new InputStreamReader(is, StandardCharsets.UTF_8);
             BufferedReader br = new BufferedReader(fr)) {
            return javaService.createJavaParser().parse(br);
        } catch (Exception e) {
            throw new ParseExceptionInFile(filename, e);
        }
    }

    // ----- parsing libraries

    /**
     * Helper method for parsing a single compilation unit directly from a file, in case no FileRepo
     * is present.
     *
     * @param filename the name of the file to read
     * @return the parsed compilation unit
     * @throws ParseExceptionInFile exceptions are wrapped into this to provide location information
     */
    private ParseResult<com.github.javaparser.ast.CompilationUnit> readWithoutFileRepo(String filename)
            throws FileNotFoundException {
        return javaService.createJavaParser().parse(new File(filename));
    }

    /**
     * parse a list of java files.
     * <p>
     * Each element of the array is treated as a filename to read in.
     *
     * @param filenames a list of strings, each element is interpreted as a file to be
     *                  read. not null.
     * @param fileRepo  the fileRepo which will store the files
     * @return a new list containing the recoder compilation units corresponding
     * to the given files.
     */
    private List<com.github.javaparser.ast.CompilationUnit> readCompilationUnitsAsFilesBare(
            String[] filenames, @Nullable FileRepo fileRepo) {
        List<com.github.javaparser.ast.CompilationUnit> cUnits = new ArrayList<>();
        parseSpecialClasses(fileRepo);
        try {
            for (String filename : filenames) {
                final ParseResult<com.github.javaparser.ast.CompilationUnit> cu;
                if (fileRepo != null) {
                    // open stream via FileRepo
                    cu = readViaFileRepo(fileRepo, filename);
                } else {
                    // fallback without FileRepo
                    cu = readWithoutFileRepo(filename);
                }
                if (cu.isSuccessful()) {
                    cUnits.add(cu.getResult().get());
                } else {
                    reportError(cu.getProblems());
                }
            }
            // transform program
            applyKeyTransformations(cUnits);
        } catch (FileNotFoundException | ParseExceptionInFile ex) {
            reportError(ex.getMessage(), ex);
        }
        return cUnits;
    }

    public static void reportError(ParseResult<?> cu) {
        reportError(cu.getProblems());
    }

    private static void reportError(List<Problem> problems) {
        for (Problem problem : problems) {
            Debug.out(problem.toString());
        }

        throw new RuntimeException("Could not parse: "
                + problems.stream().map(Object::toString).collect(Collectors.joining("\n")));
    }

    /**
     * read a compilation unit, given as a string.
     *
     * @param cUnitString a string represents a compilation unit
     * @return a KeY structured compilation unit.
     */
    public CompilationUnit readCompilationUnit(String cUnitString) {
        var cu = recoderCompilationUnits(new String[]{cUnitString}).get(0);
        return (CompilationUnit) convert2Key(cu);
    }

    /**
     * read a number of compilation units, each given as a string.
     *
     * @param contents an array of strings, each element represents a compilation
     *                 unit
     * @return a list of KeY structured compilation units.
     */
    List<com.github.javaparser.ast.CompilationUnit> recoderCompilationUnits(String[] contents) {
        parseSpecialClasses();
        List<com.github.javaparser.ast.CompilationUnit> cUnits = new ArrayList<>();
        int current = 0;
        for (String content : contents) {
            Debug.out("Reading " + trim(content));
            final var parse = javaService.createJavaParser().parse(content);
            if (parse.isSuccessful()) {
                cUnits.add(parse.getResult().get());
            } else {
                reportError(parse.getProblems());
            }
        }
        applyKeyTransformations(cUnits);
        return cUnits;
    }

    public void setClassPath(File bootClassPath, List<File> classPath) {
        this.classPath = classPath;
        this.bootClassPath = bootClassPath;
        javaService.setClassPath(bootClassPath, classPath);
    }

    /**
     * get the list of names of classes that have been created dynamically due
     * to lacking definitions.
     * <p>
     * For all classes that are referenced but not defined, an empty dummy stub
     * is created. This method returns the list of their fully qualified class
     * names.
     *
     * @return an unmodifiable list of fully qualified class names
     * @author mu, on rb's specification ;)
     */
    public List<String> getDynamicallyCreatedClasses() {
        List<String> ret = new ArrayList<>();
        if (dynamicallyCreatedCompilationUnits != null) {
            for (CompilationUnit cu : dynamicallyCreatedCompilationUnits) {
                ret.add(cu.getPrimaryTypeDeclaration().getFullName());
            }
        }
        return ret;
    }

    /**
     * This method loads the internal classes - also called the "boot" classes.
     * <p>
     * If {@link #bootClassPath} is set to null, it locates java classes that
     * are stored internally within the jar-file or the binary directory. The
     * JAVALANG.TXT file lists all files to be loaded. The files are found using
     * a special {@link JavaReduxFileCollection}.
     * <p>
     * If, however, {@link #bootClassPath} is assigned a value, this is treated
     * as a directory (not a JAR file at the moment) and all files in this
     * directory are read in. This is done using a
     * {@link DirectoryFileCollection}.
     *
     * @param fileRepo the FileRepo that provides the InputStream to resources
     */
    private void parseInternalClasses(List<com.github.javaparser.ast.CompilationUnit> rcuList,
                                      FileRepo fileRepo) throws IOException {
        FileCollection bootCollection;
        FileCollection.Walker walker;
        if (bootClassPath == null) {
            bootCollection = new JavaReduxFileCollection(services.getProfile());
            walker = bootCollection.createWalker(".java");
        } else {
            bootCollection = new DirectoryFileCollection(bootClassPath);
            walker = bootCollection.createWalker(new String[]{".java", ".jml"});
        }


        while (walker.step()) {
            var loc = walker.getCurrentDataLocation();
            try (Reader f = new BufferedReader(new InputStreamReader(walker.openCurrent(fileRepo)))) {
                var rcu = javaService.createJavaParser().parse(f);
                if (rcu.isSuccessful()) {
                    rcuList.add(rcu.getResult().get());
                } else reportError(rcu);
            }
            if (Debug.ENABLE_DEBUG) {
                Debug.out("parsed: " + loc);
            }
        }
    }

    /**
     * reads compilation units that will be treated as library classes.
     * <p>
     * Proceed as follows:
     *
     * <ol>
     * <li> If "classPath" is set and contains at least one entry
     * <ol>
     * <li>read every <code>.java</code> file within the entries (directories
     * or zip files)
     * <li>read every <code>.class</code> file within the entries
     * (directories or zip files)
     * </ol>
     * <li>else read a special collection of classes that is stored internally
     * </ol>
     *
     * @param fileRepo the FileRepo for obtaining InputStreams
     * @return
     * @throws IOException
     * @author mulbrich
     */
    private List<com.github.javaparser.ast.CompilationUnit> parseLibs(FileRepo fileRepo) throws IOException {
        JavaParser pf = javaService.createJavaParser();
        List<com.github.javaparser.ast.CompilationUnit> rcuList = new LinkedList<>();

        parseInternalClasses(rcuList, fileRepo);

        List<FileCollection> sources = new ArrayList<>();
        if (classPath != null) {
            for (File cp : classPath) {
                if (cp.isDirectory()) {
                    sources.add(new DirectoryFileCollection(cp));
                } else {
                    sources.add(new ZipFileCollection(cp));
                }
            }
        }


        // -- read jml files --
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".jml");
            while (walker.step()) {
                var currentDataLocation = walker.getCurrentDataLocation();
                try (InputStream is = walker.openCurrent(fileRepo);
                     Reader isr = new InputStreamReader(is);
                     Reader f = new BufferedReader(isr)) {
                    var rcu = pf.parse(f);
                    if (rcu.isSuccessful()) {
                        var cu = rcu.getResult().get();
                        removeCodeFromClasses(cu, false);
                        rcuList.add(cu);
                    }
                } catch (Exception ex) {
                    throw new ConvertException("Error while loading: " + walker.getCurrentDataLocation(), ex);
                }
            }
        }

        // -- read java files --
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".java");
            while (walker.step()) {
                var currentDataLocation = walker.getCurrentDataLocation();
                try (InputStream is = walker.openCurrent(fileRepo);
                     Reader isr = new InputStreamReader(is);
                     Reader f = new BufferedReader(isr)) {

                    var rcu = pf.parse(f);
                    if (rcu.isSuccessful()) {
                        var cu = rcu.getResult().get();
                        removeCodeFromClasses(cu, true);
                        rcuList.add(cu);
                    }
                } catch (Exception ex) {
                    throw new ConvertException("Error while loading: " + walker.getCurrentDataLocation(), ex);
                }
            }
        }

        /*
        // -- read class files --
        ClassFileDeclarationManager manager = new ClassFileDeclarationManager(pf);
        ByteCodeParser parser = new ByteCodeParser();
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".class");
            while (walker.step()) {
                currentDataLocation = walker.getCurrentDataLocation();
                try (InputStream is = new BufferedInputStream(walker.openCurrent(fileRepo))) {
                    ClassFile cf = parser.parseClassFile(is);
                    manager.addClassFile(cf, currentDataLocation);
                } catch (Exception ex) {
                    throw new ConvertException("Error while loading: " + walker.getCurrentDataLocation(), ex);
                }
            }
        }
        rcuList.addAll(manager.getCompilationUnits());
        */
        var rcu = pf.parse(
                "public class " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_CLASS +
                        " { public static void " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_METHOD + "() {}  }");
        if (rcu.isSuccessful()) {
            var cu = rcu.getResult().get();
            rcuList.add(cu);
        }
        return rcuList;

    }

    /**
     * removes code from a parsed compilation unit. This includes method bodies,
     * initial assignments, compile-time constants, static blocks.
     * <p>
     * This is done for classes that are read in a classpath-context. For these
     * classes only contracts (if present) are to be considered.
     * <p>
     * No need to inform changeHistory since the class is not yet registered.
     * Method bodies are set to null, i.e. all methods are stubs only
     * <p>
     * TODO remove jml-model methods (or similar) also?
     * FIXME this does not work if jml set statements are last in a method
     * TODO leave it out all together?
     */
    private void removeCodeFromClasses(com.github.javaparser.ast.CompilationUnit rcu, boolean allowMethodBody) {
        VoidVisitor<Void> v = new VoidVisitorAdapter<Void>() {
            @Override
            public void visit(MethodDeclaration n, Void arg) {
                if (!allowMethodBody && n.getBody().isPresent()) {
                    Debug.log4jWarn(
                            String.format("Method body (%s) should not be allowMethodBody: %s",
                                    n.getName(), rcu.getStorage()),
                            Recoder2KeY.class.getName());
                }
                n.setBody(null);
            }
            /*
            // This is deactivated to allow compile time constants in declaration stub files.
            // see bug #1114
            if (pe instanceof declaration.FieldSpecification) {
                declaration.FieldSpecification fieldSpec =
                    (declaration.FieldSpecification) pe;
                if(!allowMethodBody && fieldSpec.getInitializer() != null) {
                    Debug.log4jWarn("Field initializer ("+fieldSpec.getName()+") should not be allowMethodBody: "+rcu.getDataLocation(),
                          Recoder2KeY.class.getName());
                }
                fieldSpec.setInitializer(null);
            }
            */

            @Override
            public void visit(InitializerDeclaration n, Void arg) {
                if (!allowMethodBody && n.getBody() != null) {
                    Debug.log4jWarn("There should be no class initializers: " + rcu.getStorage(),
                            Recoder2KeY.class.getName());
                }
                n.setBody(null);
            }
        };
        rcu.accept(v, null);
    }


    // ----- methods dealing with blocks.

    /**
     * makes sure that the special classes (library classes) have been parsed
     * in.
     * <p>
     * If not parsed yet, the special classes are read in and converted.
     * This method throws only runtime exceptions for historical reasons.
     */
    public void parseSpecialClasses() {
        try {
            parseLibraryClasses0(null);
        } catch (Exception e) {
            reportError("An error occurred while parsing the libraries", e);
        }
    }

    /**
     * makes sure that the special classes (library classes) have been parsed
     * in.
     * <p>
     * If not parsed yet, the special classes are read in and converted.
     * This method throws only runtime exceptions for historical reasons.
     *
     * @param fileRepo the fileRepo which will store the files
     */
    public void parseSpecialClasses(FileRepo fileRepo) {
        try {
            parseLibraryClasses0(fileRepo);
        } catch (Exception e) {
            reportError("An error occurred while parsing the libraries", e);
        }
    }

    private void parseLibraryClasses0(FileRepo fileRepo) throws Exception {
        // go to special mode -> used by the converter!
        setParsingLibs(true);

        var specialClasses = parseLibs(fileRepo);
        applyKeyTransformations(specialClasses);

        // make them available to the rec2key mapping
        for (var cu : specialClasses) {
            //TODO weigl were to put the compilation unit?
            var c = convert2Key(cu);
            //getConverter().processCompilationUnit(cu, dl);
        }
        setParsingLibs(false);
    }

    /**
     * Transform a list of compilation units.
     * <p>
     * Once a compilation unit has been parsed in and prior to converting it to
     * the KeY structures, several transformations have to be performed upon it.
     * <p>
     * You can add your own Transformation here. Make sure it is in the correct
     * order.
     *
     * @param cUnits a list of compilation units, not null.
     */
    protected void applyKeyTransformations(List<com.github.javaparser.ast.CompilationUnit> cUnits) {
        final var cache = new TransformationPipelineServices.TransformerCache(cUnits);
        var pServices = new TransformationPipelineServices(javaService, cache);
        KeyJavaPipeline pipeline = KeyJavaPipeline.createDefault(pServices);
        pipeline.apply(cUnits);
    }

    /**
     * wraps a RECODER StatementBlock in a method
     * <p>
     * it is wrapped in a method called
     * <code>&lt;virtual_method_for_parsing&gt;</code>.
     *
     * @param block the StatementBlock to wrap
     * @return the enclosing MethodDeclaration
     */
    protected MethodDeclaration embedBlock(BlockStmt block) {
        MethodDeclaration mdecl = new MethodDeclaration();
        mdecl.setType(new VoidType());
        mdecl.setName("$virtual_method_for_parsing");
        mdecl.setBody(block);
        return mdecl;
    }

    /**
     * wraps a RECODER MethodDeclaration in a class
     *
     * @param mdecl   the declaration.MethodDeclaration to wrap
     * @param context the declaration.ClassDeclaration where the method
     *                has to be embedded
     * @return the enclosing declaration.ClassDeclaration
     */
    protected ClassOrInterfaceDeclaration embedMethod(MethodDeclaration mdecl, Context context) {
        var classContext = context.getClassContext();
        // add method to member declaration list
        var memberList = classContext.getMethodsByName(mdecl.getNameAsString());
        classContext.getMembers().removeAll(memberList);
        memberList.add(mdecl);
        // add method to class
        return classContext;
    }

    /**
     * creates an empty RECODER compilation unit with a temporary name.
     *
     * @return the new CompilationUnit
     */
    public Context createEmptyContext() {
        return Context.createDefault();
    }

    /**
     * create a new Context with a temporary name and make a list of variables
     * visible from within.
     *
     * @param vars a list of variables
     * @return a newly created context.
     */
    protected Context createContext(ImmutableList<ProgramVariable> vars) {
        var context = createEmptyContext();
        addProgramVariablesToClassContext(context.getClassContext(), vars);
        return context;
    }

    /**
     * add a list of variables to a context
     *
     * @param classContext context to add to
     * @param vars         vars to add
     */
    private void addProgramVariablesToClassContext(ClassOrInterfaceDeclaration classContext,
                                                   ImmutableList<ProgramVariable> vars) {

        HashMap<String, Object> names2var = new LinkedHashMap<>();
        var names = new java.util.HashSet<String>();
        var list = classContext.getMembers();

        for (ProgramVariable var : vars) {
            if (names.contains(var.name().toString())) {
                continue;
            }

            names.add(var.name().toString());

            if (var.getKeYJavaType() == null) {
                /// The program variable "variant" introduced to prove loop termination has sort
                /// "any" and, hence, no type. Parsing modalities fails on branches on which the
                /// variable exists. Therefore, it seems better to silently ignore such program
                /// variables (not making themaccessible) rather than to throw an exception.
                /// MU 01.2019
                // throw new IllegalArgumentException("Variable " + var + " has no type");
                continue;
            }
            var javaType = var.getKeYJavaType().getJavaType();
            if (javaType == null) {
                continue;
            }

            var typeName = javaType.getFullName();
            var recVar = new FieldDeclaration(null, name2typeReference(typeName), var.name().toString());
            list.add(recVar);

            //VariableSpecification rvarspec = recVar.getVariables().get(0);
            names2var.put(var.name().toString(), var.name().toString());

            //insertToMap(recVar.getVariables().get(0), keyVarSpec);
        }
    }

    /**
     * given a name as string, construct a recoder type reference from it.
     *
     * @param typeName non-null type name as string
     * @return a freshly created type reference to the given type.
     */
    private com.github.javaparser.ast.type.Type name2typeReference(String typeName) {
        var result = javaService.createJavaParser().parseType(typeName);
        if (result.isSuccessful()) {
            return result.getResult().get();
        } else {
            reportError(result);
        }
        return null;
    }

    /**
     * parses a given JavaBlock using the context to determine the right
     * references and returns a statement block of recoder.
     *
     * @param block   a String describing a java block
     * @param context CompilationUnit in which the block has to be
     *                interpreted
     * @return the parsed and resolved recoder statement block
     */
    BlockStmt recoderBlock(String block, Context context) {
        parseSpecialClasses();
        var result = javaService.createJavaParser().parseBlock(block);
        if (!result.isSuccessful()) {
            reportError(result);
        }
        var bl = result.getResult().get();
        embedMethod(embedBlock(bl), context);
        // normalise constant string expressions
        var units = Collections.singletonList(context.getCompilationUnitContext());
        applyKeyTransformations(units);
        return bl;
    }

// ----- helpers

    /**
     * parses a given JavaBlock using the context to determine the right
     * references
     *
     * @param block   a String describing a java block
     * @param context CompilationUnit in which the block has to be
     *                interprested
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlock(String block, Context context) {
        var sb = recoderBlock(block, context);
        return JavaBlock.createJavaBlock((StatementBlock) convert2Key(sb));
    }

    /**
     * parses a given JavaBlock using the context to determine the right
     * references using an empty context
     *
     * @param block a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlockWithEmptyContext(String block) {
        return readBlock(block, createEmptyContext());
    }

// ----- error handling

    /**
     * parses a given JavaBlock using a namespace to determine the right
     * references using an empty context. The variables of the namespace are
     * used to create a new class context
     *
     * @param s a String describing a java block
     * @return the parsed and resolved JavaBlock
     */
    public JavaBlock readBlockWithProgramVariables(Namespace<IProgramVariable> varns, String s) {
        Iterator<IProgramVariable> it = varns.allElements().iterator();
        ImmutableList<ProgramVariable> pvs = ImmutableSLList.nil();
        while (it.hasNext()) {
            var n = it.next();
            if (n instanceof ProgramVariable) {
                pvs = pvs.append((ProgramVariable) n); //preserve the order (nested namespaces!)
            }
        }
        return readBlock(s, createContext(pvs));
    }

    public KeYJavaType getSuperArrayType() {
        return null; //TODO weigl
    }

    public boolean parsedSpecial() {
        return false;
    }

    public Set<?> elemsKeY() {
        return null;
    }

    public Node toRecoder(KeYJavaType kjt) {
        return null;
    }

    public Type toRecoder(de.uka.ilkd.key.java.abstraction.Type n) {
        return null;
    }

    public ProgramElement toKeY(MethodUsage rm) {
        return null;
    }

    public ProgramElement toKeY(Type t) {
        return null;
    }
}