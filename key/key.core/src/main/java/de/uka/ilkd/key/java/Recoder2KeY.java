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

package de.uka.ilkd.key.java;

import com.github.javaparser.ast.body.MethodDeclaration;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.NullType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.transformations.*;
import de.uka.ilkd.key.java.transformations.pipeline.JMLTransformer;
import de.uka.ilkd.key.java.transformations.pipeline.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Paths;
import java.util.*;

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
 *
 * @see Recoder2KeYConverter
 * @see Recoder2KeYTypeConverter
 */

public class Recoder2KeY implements JavaReader {

    /**
     * counter used to enumerate the anonymous implicit classes
     */
    private static int interactCounter = 0;
    private final Services services;
    /**
     * the set of File objects that describes the classpath to be searched
     * for classes.
     * it may contain a null file which indicates that the default classes are
     * not to be read.
     */
    private List<File> classPath;
    /**
     * the File object that describes the directory from which the internal
     * classes are to be read. They are read in differently - therefore the
     * second category. A null value indicates that the boot classes are to
     * be read from an internal repository.
     */
    private File bootClassPath;
    /**
     * this mapping stores the relation between recoder and KeY entities in a
     * bidirectional way.
     * <p>
     * It is used for syntactical structures and types.
     */
    private final KeYRecoderMapping mapping;
    /**
     * Recoder's serviceConfiguration that is used throughout this process.
     */
    private final TransformationPipelineServices servConf;
    /**
     * this flag indicates whether we are currently parsing library classes
     * (special classes)
     */
    private boolean parsingLibs = false;
    /**
     * the object that handles the transformation from recoder AST to KeY AST
     */
    private final Recoder2KeYConverter converter;
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

    /**
     * create a new Recoder2KeY transformation object.
     * <p>
     * The converter and type converter associated with this object will be
     * created. Several properties of the recoder framework will be set up.
     * <p>
     * The classpath is set to null, the mapping is retrieved from the services,
     * as well as the underlying type converter
     *
     * @param servConf the service configuration to be used, not null
     * @param rec2key  the mapping to store mapped types and mapped ASTs to, not null
     * @param nss      the namespaces to work upon, not null
     * @param tc       the type converter, not null
     */
    public Recoder2KeY(Services services, TransformationPipelineServices servConf, KeYRecoderMapping rec2key, NamespaceSet nss, TypeConverter tc) {
        this(services, servConf, null, rec2key, nss, tc);
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
        this(services, services.getJavaInfo().getKeYProgModelInfo().getServConf(), null, services.getJavaInfo().rec2key(), nss, services.getTypeConverter());
    }

    /**
     * create a new Recoder2KeY transformation object.
     * <p>
     * The converter and type converter associated with this object will be
     * created. Several properties of the recoder framework will be set up.
     *
     * @param servConf  the service configuration to be used, not null
     * @param classPath the classpath to look up source files, ignored if null
     * @param rec2key   the mapping to store mapped types and mapped ASTs to, not null
     * @param nss       the namespaces to work upon, not null
     * @param tc        the type converter, not null
     * @throws IllegalArgumentException if arguments are not valid (null e.g.)
     */
    private Recoder2KeY(Services services, KeYTransformationPipelineServices servConf, String classPath,
                        KeYRecoderMapping rec2key, NamespaceSet nss, TypeConverter tc) {

        if (servConf == null)
            throw new IllegalArgumentException("service configuration is null");

        if (rec2key == null)
            throw new IllegalArgumentException("rec2key mapping is null");

        if (nss == null)
            throw new IllegalArgumentException("namespaces is null");

        if (!(servConf.getProjectSettings().getErrorHandler() instanceof KeYRecoderExcHandler))
            throw new IllegalArgumentException("Recoder2KeY needs a KeyRecoderExcHandler as exception handler");

        this.services = services;
        this.servConf = servConf;
        this.mapping = rec2key;
        this.converter = makeConverter(services, nss);
        this.typeConverter = new Recoder2KeYTypeConverter(services, tc, nss, this);

        // do not look up classes anywhere but in the included classes
        // or the specified classpaths
        servConf.getProjectSettings().setProperty(PropertyNames.CLASS_SEARCH_MODE, "");

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
     * create the ast converter. This is overwritten in SchemaRecoder2KeY to use
     * schema-aware converters.
     *
     * @param services
     * @param nss      the namespaces provided to the constructor
     * @return a newley created converter
     */
    protected Recoder2KeYConverter makeConverter(Services services, NamespaceSet nss) {
        return new Recoder2KeYConverter(this, services, nss);
    }

    /**
     * return the associated converter object
     *
     * @return not null
     */
    public Recoder2KeYConverter getConverter() {
        return converter;
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

    public KeYTransformationPipelineServices getServiceConfiguration() {
        return servConf;
    }

    public KeYRecoderMapping rec2key() {
        return mapping;
    }

    private void insertToMap(ModelElement r, ModelElement k) {
        if (r != null && k != null) {
            rec2key().put(r, k);
        } else {
            Debug.out("Rec2Key.insertToMap: Omitting entry  (r = " + r + " -> k = " + k + ")");
        }
    }

    /**
     * parse a list of java files and transform it to the corresponding KeY
     * entities.
     * <p>
     * Each element of the array is treated as a filename to read in.
     *
     * @param cUnitStrings a list of strings, each element is interpreted as a file to be
     *                     read. not null.
     * @param fileRepo     the fileRepo which will store the files
     * @return a new list containing the recoder compilation units corresponding
     * to the given files.
     * @throws ParseExceptionInFile any exception occurring while treating the file is wrapped
     *                              into a parse exception that contains the filename.
     */

    public de.uka.ilkd.key.java.CompilationUnit[] readCompilationUnitsAsFiles(String[] cUnitStrings, FileRepo fileRepo) {
        List<CompilationUnit> cUnits = recoderCompilationUnitsAsFiles(cUnitStrings, fileRepo);
        de.uka.ilkd.key.java.CompilationUnit[] result = new de.uka.ilkd.key.java.CompilationUnit[cUnits.size()];
        for (int i = 0, sz = cUnits.size(); i < sz; i++) {
            Debug.out("converting now " + cUnitStrings[i]);
            try {
                CompilationUnit cu = cUnits.get(i);
                result[i] = getConverter().processCompilationUnit(cu, cu.getDataLocation());
            } catch (Exception e) {
                throw new ParseExceptionInFile(cUnitStrings[i], e);
            }
        }
        return result;
    }

    /**
     * Helper method for parsing a single compilation unit when a FileRepo is present.
     *
     * @param fileRepo the FileRepo that provides the InputStream
     * @param filename the name of the file to read
     * @return the parsed compilation unit
     * @throws ParseExceptionInFile exceptions are wrapped into this to provide location information
     */
    private CompilationUnit readViaFileRepo(FileRepo fileRepo, String filename)
            throws ParseExceptionInFile {
        try (InputStream is = fileRepo.getInputStream(Paths.get(filename));
             Reader fr = new InputStreamReader(is, StandardCharsets.UTF_8);
             BufferedReader br = new BufferedReader(fr)) {
            return servConf.getProgramFactory().parseCompilationUnit(br);
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
    private CompilationUnit readWithoutFileRepo(String filename) {
        try (Reader fr = new FileReader(filename);
             BufferedReader br = new BufferedReader(fr)) {
            return servConf.getProgramFactory().parseCompilationUnit(br);
        } catch (Exception e) {
            throw new ParseExceptionInFile(filename, e);
        }
    }

    /**
     * parse a list of java files.
     * <p>
     * Each element of the array is treated as a filename to read in.
     *
     * @param cUnitStrings a list of strings, each element is interpreted as a file to be
     *                     read. not null.
     * @param fileRepo     the fileRepo which will store the files
     * @return a new list containing the recoder compilation units corresponding
     * to the given files.
     */
    private List<CompilationUnit> recoderCompilationUnitsAsFiles(String[] cUnitStrings, FileRepo fileRepo) {
        List<CompilationUnit> cUnits = new ArrayList<>();
        parseSpecialClasses(fileRepo);
        try {
            for (String filename : cUnitStrings) {
                final CompilationUnit cu;

                if (fileRepo != null) {
                    // open stream via FileRepo
                    cu = readViaFileRepo(fileRepo, filename);
                } else {
                    // fallback without FileRepo
                    cu = readWithoutFileRepo(filename);
                }

                cu.setDataLocation(new DataFileLocation(filename));
                cUnits.add(cu);
            }

            final ChangeHistory changeHistory = servConf.getChangeHistory();
            for (int i = 0, sz = cUnits.size(); i < sz; i++) {
                cUnits.get(i).makeAllParentRolesValid();
                changeHistory.attached(cUnits.get(i));
            }

            if (changeHistory.needsUpdate()) {
                changeHistory.updateModel();
            }

            // transform program
            transformModel(cUnits);
        } catch (Exception ex) {
            if (ex.getCause() instanceof UnresolvedReferenceException) {
                String extraMsg = "Consider using a classpath if this is a classtype that cannot be resolved\n";
                reportError(extraMsg + ex.getCause().getMessage(), ex);
            } else {
                reportError(ex.getMessage(), ex);
            }
        }
        return cUnits;
    }

    /**
     * read a compilation unit, given as a string.
     *
     * @param cUnitString a string represents a compilation unit
     * @return a KeY structured compilation unit.
     */
    public de.uka.ilkd.key.java.CompilationUnit readCompilationUnit(String cUnitString) {
        final CompilationUnit cc = recoderCompilationUnits(new String[]{cUnitString}).get(0);
        return (de.uka.ilkd.key.java.CompilationUnit) getConverter().process(cc);
    }

    /**
     * read a number of compilation units, each given as a string.
     *
     * @param cUnitStrings an array of strings, each element represents a compilation
     *                     unit
     * @return a list of KeY structured compilation units.
     */
    List<CompilationUnit> recoderCompilationUnits(String[] cUnitStrings) {
        parseSpecialClasses();
        List<CompilationUnit> cUnits = new ArrayList<CompilationUnit>();
        int current = 0;
        Reader sr = null;
        try {
            for (int i = 0; i < cUnitStrings.length; i++) {
                current = i;
                Debug.out("Reading " + trim(cUnitStrings[i]));
                sr = new BufferedReader(new StringReader(cUnitStrings[i]));
                cUnits.add(servConf.getProgramFactory().parseCompilationUnit(sr));
            }
            // run cross referencer
            final ChangeHistory changeHistory = servConf.getChangeHistory();
            for (int i = 0, sz = cUnits.size(); i < sz; i++) {
                current = i;
                cUnits.get(i).makeAllParentRolesValid();
                changeHistory.attached(cUnits.get(i));
            }

            if (changeHistory.needsUpdate()) {
                changeHistory.updateModel();
            }
            // transform program

            transformModel(cUnits);
        } catch (IOException ioe) {
            Debug.out("recoder2key: IO Error when reading" + "compilation unit " + cUnitStrings[current], ioe);
            reportError("IOError reading java program " + cUnitStrings[current] + ". May be file not found or missing permissions.", ioe);
        } catch (Exception pe) {
            Debug.out("recoder2key: Recoder Parser Error when" + "reading a comiplation unit " + cUnitStrings[current], pe);
            if (pe.getCause() != null) {
                reportError(pe.getCause().getMessage(), pe.getCause());
            } else {
                reportError(pe.getMessage(), pe);
            }
        } finally {
            if (sr != null) {
                try {
                    sr.close();
                } catch (IOException e) {
                    reportError("IOError reading java program " +
                            cUnitStrings[current] + ". May be file not found or missing permissions.", e);
                }
            }
        }
        return cUnits;
    }

    public void setClassPath(File bootClassPath, List<File> classPath) {
        this.classPath = classPath;
        this.bootClassPath = bootClassPath;
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
        List<String> ret = new ArrayList<String>();
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
    private void parseInternalClasses(
            ProgramFactory pf, List<CompilationUnit> rcuList, FileRepo fileRepo) throws IOException {

        FileCollection bootCollection;
        FileCollection.Walker walker = null;
        if (bootClassPath == null) {
            bootCollection = new JavaReduxFileCollection(services.getProfile());
            walker = bootCollection.createWalker(".java");
        } else {
            bootCollection = new DirectoryFileCollection(bootClassPath);
            walker = bootCollection.createWalker(new String[]{".java", ".jml"});
        }


        while (walker.step()) {
            DataLocation loc = walker.getCurrentDataLocation();
            try (InputStream is = walker.openCurrent(fileRepo);
                 Reader isr = new InputStreamReader(is);
                 Reader f = new BufferedReader(isr)) {

                CompilationUnit rcu = pf.parseCompilationUnit(f);
                rcu.setDataLocation(loc);
                // done by parser : rcu.makeAllParentRolesValid();
                rcuList.add(rcu);
            } catch (Exception ex) {
                throw new ParseExceptionInFile(loc.toString(), ex);
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
     * @throws ParserException
     * @throws IOException
     * @throws ParseException
     * @author mulbrich
     */
    private List<CompilationUnit> parseLibs(FileRepo fileRepo) throws IOException {
        ProgramFactory pf = servConf.getProgramFactory();
        List<CompilationUnit> rcuList = new LinkedList<CompilationUnit>();
        List<FileCollection> sources = new ArrayList<FileCollection>();

        parseInternalClasses(pf, rcuList, fileRepo);

        if (classPath != null) {
            for (File cp : classPath) {
                if (cp.isDirectory()) {
                    sources.add(new DirectoryFileCollection(cp));
                } else {
                    sources.add(new ZipFileCollection(cp));
                }
            }
        }

        /* While the resources are read (and possibly copied) via the FileRepo, the data location
         * is left as it is. This leaves the line information intact. */
        DataLocation currentDataLocation = null;

        // -- read jml files --
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".jml");
            while (walker.step()) {
                currentDataLocation = walker.getCurrentDataLocation();
                try (InputStream is = walker.openCurrent(fileRepo);
                     Reader isr = new InputStreamReader(is);
                     Reader f = new BufferedReader(isr)) {

                    CompilationUnit rcu = pf.parseCompilationUnit(f);
                    rcu.setDataLocation(currentDataLocation);
                    removeCodeFromClasses(rcu, false);
                    rcuList.add(rcu);
                } catch (Exception ex) {
                    throw new ConvertException("Error while loading: " + walker.getCurrentDataLocation(), ex);
                }
            }
        }

        // -- read java files --
        for (FileCollection fc : sources) {
            FileCollection.Walker walker = fc.createWalker(".java");
            while (walker.step()) {
                currentDataLocation = walker.getCurrentDataLocation();
                try (InputStream is = walker.openCurrent(fileRepo);
                     Reader isr = new InputStreamReader(is);
                     Reader f = new BufferedReader(isr)) {

                    CompilationUnit rcu = pf.parseCompilationUnit(f);
                    rcu.setDataLocation(currentDataLocation);
                    removeCodeFromClasses(rcu, true);
                    rcuList.add(rcu);
                } catch (Exception ex) {
                    throw new ConvertException("Error while loading: " + walker.getCurrentDataLocation(), ex);
                }
            }
        }

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

        CompilationUnit rcu = pf.parseCompilationUnit(
                new StringReader("public class " +
                        JavaInfo.DEFAULT_EXECUTION_CONTEXT_CLASS + " { public static void " + JavaInfo.DEFAULT_EXECUTION_CONTEXT_METHOD + "() {}  }"));
        rcuList.add(rcu);

        return rcuList;

    }

    /*
     * removes code from a parsed compilation unit. This includes method bodies,
     * initial assignments, compile-time constants, static blocks.
     *
     * This is done for classes that are read in a classpath-context. For these
     * classes only contracts (if present) are to be considered.
     *
     * No need to inform changeHistory since the class is not yet registered.
     * Method bodies are set to null, i.e. all methods are stubs only
     *
     * TODO remove jml-model methods (or similar) also?
     * FIXME this does not work if jml set statements are last in a method
     * TODO leave it out all together?
     */
    private void removeCodeFromClasses(CompilationUnit rcu, boolean allowed) {
        TreeWalker tw = new TreeWalker(rcu);

        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof MethodDeclaration) {
                MethodDeclaration methDecl = (MethodDeclaration) pe;
                if (!allowed && methDecl.getBody() != null) {
                    Debug.log4jWarn("Method body (" + methDecl.getName() + ") should not be allowed: " + rcu.getDataLocation(),
                            Recoder2KeY.class.getName());
                }
                methDecl.setBody(null);
            }
            /*
            // This is deactivated to allow compile time constants in declaration stub files.
            // see bug #1114
            if (pe instanceof declaration.FieldSpecification) {
                declaration.FieldSpecification fieldSpec =
                    (declaration.FieldSpecification) pe;
                if(!allowed && fieldSpec.getInitializer() != null) {
                    Debug.log4jWarn("Field initializer ("+fieldSpec.getName()+") should not be allowed: "+rcu.getDataLocation(),
                          Recoder2KeY.class.getName());
                }
                fieldSpec.setInitializer(null);
            }
            */
            if (pe instanceof ClassInitializer) {
                ClassInitializer classInit = (ClassInitializer) pe;
                if (!allowed && classInit.getBody() != null) {
                    Debug.log4jWarn("There should be no class initializers: " + rcu.getDataLocation(),
                            Recoder2KeY.class.getName());
                }
                classInit.setBody(null);
            }
        }
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

    private void parseLibraryClasses0(FileRepo fileRepo)
            throws ParseException, IOException, ParserException {
        if (mapping.parsedSpecial()) {
            return;
        }

        // go to special mode -> used by the converter!
        setParsingLibs(true);

        List<CompilationUnit> specialClasses = parseLibs(fileRepo);

        ChangeHistory changeHistory = servConf.getChangeHistory();
        for (int i = 0, sz = specialClasses.size(); i < sz; i++) {
            specialClasses.get(i).makeAllParentRolesValid();
            // TODO if duplicated files, take first one only!
            changeHistory.attached(specialClasses.get(i));
        }


        CrossReferenceSourceInfo sourceInfo = servConf.getCrossReferenceSourceInfo();
        assert sourceInfo instanceof KeYCrossReferenceSourceInfo :
                "SourceInfo is not of type KeYCrossReferenceSourceInfo";
        KeYCrossReferenceSourceInfo keySourceInfo =
                (KeYCrossReferenceSourceInfo) sourceInfo;

        keySourceInfo.setIgnoreUnresolvedClasses(true);

        if (changeHistory.needsUpdate()) {
            changeHistory.updateModel();
        }

        dynamicallyCreatedCompilationUnits = keySourceInfo.getCreatedStubClasses();
        specialClasses.addAll(dynamicallyCreatedCompilationUnits);
        keySourceInfo.setIgnoreUnresolvedClasses(false);

        changeHistory.updateModel();

        transformModel(specialClasses);

//        NameInfo ni = servConf.getNameInfo();
//        System.out.println("Known types:");
//        for(ClassType ct : ni.getClassTypes()) {
//            System.out.println(ct.getFullName());
//        }

        // make them available to the rec2key mapping
        for (CompilationUnit cu : specialClasses) {
            DataLocation dl = cu.getOriginalDataLocation();
            assert dl != null : "DataLocation not set on " + cu.toSource();
            getConverter().processCompilationUnit(cu, dl);
        }

        // Ensure that rec2key is complete (at least the NullType needs to be available!)
        if (!rec2key().mapped(servConf.getNameInfo().getNullType())) {
            Sort objectSort = services.getNamespaces().sorts().lookup(new Name("java.lang.Object"));
            assert objectSort != null;
            NullSort nullSort = new NullSort(objectSort);
            KeYJavaType result = new KeYJavaType(NullType.JAVA_NULL, nullSort);
            if (services.getNamespaces().sorts().lookup(nullSort.name()) == null) {
                services.getNamespaces().sorts().add(nullSort);
            }
            rec2key().put(servConf.getNameInfo().getNullType(), result);
        }

        // tell the mapping that we have parsed the special classes
        rec2key().parsedSpecial(true);

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

    protected void transformModel(List<com.github.javaparser.ast.CompilationUnit> cUnits) {
        TransformerCache cache = new TransformerCache(cUnits);

        ConstructorNormalformBuilder cnb;

        JavaTransformer[] transformer = new JavaTransformer[]{
                //new EnumClassBuilder(servConf),
                new JMLTransformer(servConf),
                new ImplicitFieldAdder(servConf),
                new InstanceAllocationMethodBuilder(servConf),
                cnb = new ConstructorNormalformBuilder(servConf),
                new ClassPreparationMethodBuilder(servConf),
                new ClassInitializeMethodBuilder(servConf),
                new PrepareObjectBuilder(servConf),
                new CreateBuilder(servConf),
                new CreateObjectBuilder(servConf),
                new LocalClassTransformation(servConf),
                new ConstantStringExpressionEvaluator(servConf)
        };


        final ChangeHistory cHistory = servConf.getChangeHistory();
        for (JavaTransformer aTransformer : transformer) {
            if (Debug.ENABLE_DEBUG) {
                Debug.out("current transformer : " + aTransformer);
            }
            aTransformer.execute();
        }

        converter.locClass2finalVar = cnb.getLocalClass2FinalVar();

        if (cHistory.needsUpdate()) {
            cHistory.updateModel();
        }

        // recoder changes the data location to some imaginary files
        // undo this by setting the original locations
        for (com.github.javaparser.ast.CompilationUnit cu : cUnits) {
            cu.setDataLocation(cu.getOriginalDataLocation());
        }
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
    protected MethodDeclaration embedBlock(StatementBlock block) {

        /*
         * MethodDeclaration(modifiers,return type,Identifier, parameters,
         * throws, StatementBlock)
         */
        declaration.MethodDeclaration mdecl = new declaration.MethodDeclaration(null, null, new ImplicitIdentifier(
                "<virtual_method_for_parsing>"), null, null, block);
        mdecl.makeParentRoleValid();
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
    protected declaration.ClassDeclaration embedMethod(declaration.MethodDeclaration mdecl, Context context) {

        declaration.ClassDeclaration classContext = context.getClassContext();

        // add method to member declaration list
        ASTList<declaration.MemberDeclaration> memberList = classContext.getMembers();

        if (memberList == null) {
            memberList = new ASTArrayList<declaration.MemberDeclaration>(1);
            classContext.setMembers(memberList);
        }

        for (int i = 0, sz = memberList.size(); i < sz; i++) {
            if (memberList.get(i) instanceof declaration.MethodDeclaration) {
                declaration.MethodDeclaration olddecl = (declaration.MethodDeclaration) memberList.get(i);
                if (olddecl.getName().equals(mdecl.getName())) {
                    memberList.remove(i);
                }
            }
        }
        memberList.add(mdecl);

        // add method to class

        classContext.setProgramModelInfo(servConf.getCrossReferenceSourceInfo());
        classContext.makeParentRoleValid();
        return classContext;
    }

    /**
     * creates an empty RECODER compilation unit with a temporary name.
     *
     * @return the new CompilationUnit
     */
    public Context createEmptyContext() {
        declaration.ClassDeclaration classContext = interactClassDecl();
        return new Context(servConf, classContext);
    }

    /**
     * create a new context with a temporary name and make a list of variables
     * visible from within. Use the default source info.
     *
     * @param pvs a list of variables
     * @return a newly created context.
     */

    protected Context createContext(ImmutableList<ProgramVariable> pvs) {
        return createContext(pvs, servConf.getCrossReferenceSourceInfo());
    }

    /**
     * create a new Context with a temporary name and make a list of variables
     * visible from within.
     *
     * @param vars a list of variables
     * @param csi  a special source info
     * @return a newly created context.
     */
    protected Context createContext(ImmutableList<ProgramVariable> vars, recoder.service.CrossReferenceSourceInfo csi) {
        declaration.ClassDeclaration classContext = interactClassDecl();
        addProgramVariablesToClassContext(classContext, vars, csi);
        return new Context(servConf, classContext);
    }

    /**
     * add a list of variables to a context
     *
     * @param classContext context to add to
     * @param vars         vars to add
     */
    private void addProgramVariablesToClassContext(declaration.ClassDeclaration classContext, ImmutableList<ProgramVariable> vars,
                                                   recoder.service.CrossReferenceSourceInfo csi) {

        HashMap<String, declaration.VariableSpecification> names2var =
                new LinkedHashMap<String, declaration.VariableSpecification>();
        Iterator<ProgramVariable> it = vars.iterator();
        java.util.HashSet<String> names = new java.util.HashSet<String>();
        ASTList<declaration.MemberDeclaration> list = classContext.getMembers();

        // perhaps install a new list for the members of the class context
        if (list == null) {
            list = new ASTArrayList<declaration.MemberDeclaration>(1);
            classContext.setMembers(list);
        }

        l:
        while (it.hasNext()) {
            VariableSpecification keyVarSpec;
            ProgramVariable var = it.next();
            if (names.contains(var.name().toString())) {
                continue l;
            }
            names.add(var.name().toString());
            keyVarSpec = lookupVarSpec(var);
            if (keyVarSpec == null) {
                keyVarSpec = new FieldSpecification(var);
            }

            if (var.getKeYJavaType() == null) {
                /// The program variable "variant" introduced to prove loop termination has sort
                /// "any" and, hence, no type. Parsing modalities fails on branches on which the
                /// variable exists. Therefore, it seems better to silently ignore such program
                /// variables (not making themaccessible) rather than to throw an exception.
                /// MU 01.2019
                // throw new IllegalArgumentException("Variable " + var + " has no type");
                continue l;
            }

            String typeName = "";
            Type javaType = var.getKeYJavaType().getJavaType();
            if (javaType == null) continue;
            typeName = javaType.getFullName();

            declaration.FieldDeclaration recVar = new declaration.FieldDeclaration(null, name2typeReference(typeName),
                    new ExtendedIdentifier(keyVarSpec.getName()), null);

            list.add(recVar);
            classContext.makeAllParentRolesValid();
            declaration.VariableSpecification rvarspec = recVar.getVariables().get(0);
            names2var.put(var.name().toString(), rvarspec);

            rvarspec.setProgramModelInfo(csi);
            insertToMap(recVar.getVariables().get(0), keyVarSpec);
        }

        ((KeYCrossReferenceSourceInfo) csi).setNames2Vars(names2var);
        servConf.getChangeHistory().updateModel();
    }

    /**
     * look up in the mapping the variable specification for a program variable.
     * <p>
     * used by addProgramVariablesToClassContext
     */
    private VariableSpecification lookupVarSpec(ProgramVariable pv) {
        for (final Object o : mapping.elemsKeY()) {
            if ((o instanceof VariableSpecification) && ((VariableSpecification) o).getProgramVariable() == pv) {
                return (VariableSpecification) o;
            }
        }
        return null;
    }

    /**
     * given a name as string, construct a recoder type reference from it.
     *
     * @param typeName non-null type name as string
     * @return a freshly created type reference to the given type.
     */
    private reference.TypeReference name2typeReference(String typeName) {
        reference.PackageReference pr = null;
        String baseType = TypeNameTranslator.getBaseType(typeName);
        int idx = baseType.indexOf('.');
        int lastIndex = 0;
        String anonType = "";
        while (idx != -1 && baseType.charAt(lastIndex) >= 'a'
                && baseType.charAt(lastIndex) <= 'z') {
            String s = baseType.substring(lastIndex, idx);
            pr = new reference.PackageReference
                    (pr, new Identifier(s));
            lastIndex = idx + 1;
            idx = baseType.indexOf('.', lastIndex);
        }
        baseType = anonType + baseType;
        Identifier typeId;
        if (baseType.charAt(0) == '<') {
            typeId = new ImplicitIdentifier(baseType.substring(lastIndex));
        } else {
            typeId = new ObjectTypeIdentifier(baseType.substring(lastIndex));
        }
        reference.TypeReference result =
                new reference.TypeReference(pr, typeId);
        result.setDimensions(TypeNameTranslator.getDimensions(typeName));
        return result;
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
    StatementBlock recoderBlock(String block, Context context) {
        StatementBlock bl = null;
        parseSpecialClasses();
        Reader sr = null;
        try {
            sr = new BufferedReader(new StringReader(block));
            bl = servConf.getProgramFactory().parseStatementBlock(sr);
            bl.makeAllParentRolesValid();
            embedMethod(embedBlock(bl), context);
            context.getCompilationUnitContext().makeParentRoleValid();
            // servConf.getCrossReferenceSourceInfo().register(bl);
            // register() is deprecated. so use this instead:
            servConf.getChangeHistory().attached(bl);
            servConf.getChangeHistory().attached(context.getCompilationUnitContext());
            servConf.getChangeHistory().updateModel();

            // normalise constant string expressions
            List<CompilationUnit> cunits = new ArrayList<CompilationUnit>();
            cunits.add(context.getCompilationUnitContext());
            final JavaTransformer.TransformerCache cache = new JavaTransformer.TransformerCache(cunits);
            new ConstantStringExpressionEvaluator(servConf, cache).execute();
        } catch (de.uka.ilkd.key.util.ExceptionHandlerException e) {
            if (e.getCause() != null) {
                reportError(e.getCause().getMessage(), e.getCause());
            } else {
                reportError(e.getMessage(), e);
            }
        } catch (recoder.service.UnresolvedReferenceException e) {
            reportError("Could not resolve reference:" + e.getUnresolvedReference(), e);
        } catch (recoder.parser.ParseException e) {
            if (e.getCause() != null) {
                reportError(e.getCause().getMessage(), e.getCause());
            } else {
                reportError(e.getMessage(), e);
            }
        } catch (recoder.ModelException e) {
            if (e.getCause() != null) {
                reportError(e.getCause().getMessage(), e.getCause());
            } else {
                reportError(e.getMessage(), e);
            }
        } catch (recoder.ParserException e) {
            if (e.getCause() != null) {
                reportError(e.getCause().getMessage(), e.getCause());
            } else {
                reportError(e.getMessage(), e);
            }
        } catch (IOException e) {
            Debug.out("recoder2key: IOException detected in: " + block, e);
            block = trim(block, 25);
            reportError("Could not access data stream " + "(e.g. file not found, wrong permissions) " + "when reading " + block + ": " + trim(e.getMessage()),
                    e);
        } catch (NullPointerException e) {
            // to retrieve a more precise message we would need to patch Recoder
            reportError("Recoder parser threw exception in block:\n" + block + "\n Probably a misspelled identifier name.", e);
        } catch (Exception e) {
            reportError(e.getMessage(), e);
        } finally {
            if (sr != null) {
                try {
                    sr.close();
                } catch (IOException e) {
                }
            }
        }
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

        StatementBlock sb = recoderBlock(block, context);
        JavaBlock jb = JavaBlock.createJavaBlock((StatementBlock) getConverter().process(sb));
        return jb;
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
            Named n = it.next();
            if (n instanceof ProgramVariable) {
                pvs = pvs.append((ProgramVariable) n); //preserve the order (nested namespaces!)
            }
        }
        return readBlock(s, createContext(pvs));
    }

    /**
     * make a new classdeclaration with a temporary name.
     * <p>
     * The name is a unique implicit identifier.
     *
     * @return a newly created recoder ClassDeclaration with a unique name
     */
    private ClassDeclaration interactClassDecl() {
        ClassDeclaration classContext = new ClassDeclaration(null,
                new ImplicitIdentifier("<virtual_class_for_parsing" + interactCounter + ">"), null, null, null);
        interactCounter++;
        classContext.setProgramModelInfo(servConf.getCrossReferenceSourceInfo());
        return classContext;
    }

}