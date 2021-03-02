// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.relational;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.abstractexecution.refinity.model.FunctionDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.NullarySymbolDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.PredicateDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.relational.AERelationalModel;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Converts an AE Relational Model to a KeY proof bundle.
 * 
 * @author Dominic Steinhoefel
 */
public class RelationalProofBundleConverter {
    private static final String JAVA_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/relational/Problem.java";
    private static final String KEY_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/relational/refinityRelationalProblem.key";

    private static final String RELATION = "<RELATION>";
    private static final String PRECONDITION = "<PRECONDITION>";
    private static final String INIT_VARS = "<INIT_VARS>";
    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String BODY1 = "<BODY1>";
    private static final String BODY2 = "<BODY2>";
    private static final String CONTEXT = "<CONTEXT>";
    private static final String PARAMS = "<PARAMS>";
    private static final String RESULT_SEQ_1 = "<RESULT_SEQ_1>";
    private static final String RESULT_SEQ_2 = "<RESULT_SEQ_2>";
    private static final String ADDITIONAL_PREMISES = "<ADDITIONAL_PREMISES>";
    private static final String PROOF = "<PROOF>";

    // Special Keywords
    private static final String RESULT_1 = "\\result_1";
    private static final String RESULT_2 = "\\result_2";
    private static final String RESULT = "result";

    public static final String RES1 = "_res1";
    public static final String RES2 = "_res2";
    public static final String EXC = "exc";

    private final AERelationalModel model;
    private final Optional<String> proofString;
    private final String javaScaffold;
    private final String keyScaffold;
    private final Optional<File> keyFileToUse;

    /**
     * @param model The model to convert.
     * @throws IOException           If the resource files are found, but could not
     *                               be loaded.
     * @throws IllegalStateException If the required resource files could not be
     *                               found.
     */
    public RelationalProofBundleConverter(AERelationalModel model)
            throws IOException, IllegalStateException {
        this(model, null, null);
    }

    /**
     * @param model       The model to convert.
     * @param proofString If non-null, the given string will be appended to the
     *                    generated KeY file. For certificate checking.
     * @throws IOException           If the resource files are found, but could not
     *                               be loaded.
     * @throws IllegalStateException If the required resource files could not be
     *                               found.
     */
    public RelationalProofBundleConverter(AERelationalModel model, String proofString)
            throws IOException, IllegalStateException {
        this(model, proofString, null);
    }

    /**
     * @param model        The model to convert.
     * @param keyFileToUse If non-null, will use the contents of this file instead
     *                     of the scaffold file generated from the model. Used
     *                     primarily for reloading in automated tests.
     * @throws IOException           If the resource files are found, but could not
     *                               be loaded.
     * @throws IllegalStateException If the required resource files could not be
     *                               found.
     */
    public RelationalProofBundleConverter(AERelationalModel model, File keyFileToUse)
            throws IOException, IllegalStateException {
        this(model, null, keyFileToUse);
    }

    /**
     * @param model        The model to convert.
     * @param proofString  If non-null, the given string will be appended to the
     *                     generated KeY file. For certificate checking.
     * @param keyFileToUse If non-null, will use the contents of this file instead
     *                     of the scaffold file generated from the model. Used
     *                     primarily for reloading in automated tests.
     * @throws IOException           If the resource files are found, but could not
     *                               be loaded.
     * @throws IllegalStateException If the required resource files could not be
     *                               found.
     */
    public RelationalProofBundleConverter(AERelationalModel model, String proofString,
            File keyFileToUse) throws IOException, IllegalStateException {
        this.model = model;
        this.proofString = Optional.ofNullable(proofString);
        this.keyFileToUse = Optional.ofNullable(keyFileToUse);

        final InputStream javaScaffoldIS = RelationalProofBundleConverter.class
                .getResourceAsStream(JAVA_PROBLEM_FILE_SCAFFOLD);
        final InputStream keyScaffoldIS = RelationalProofBundleConverter.class
                .getResourceAsStream(KEY_PROBLEM_FILE_SCAFFOLD);
        if (javaScaffoldIS == null || keyScaffoldIS == null) {
            throw new IllegalStateException("Could not load required resource files.");
        }

        javaScaffold = IOUtil.readFrom(javaScaffoldIS);
        keyScaffold = IOUtil.readFrom(keyScaffoldIS);
    }

    /**
     * Saves the bundle to the given file.
     * 
     * @param file The output file. Has to end in ".zproof".
     * @return The {@link BundleSaveResult}.
     * @throws IOException
     */
    public BundleSaveResult save(final File file) throws IOException {
        assert file.getName().endsWith(".zproof");

        // NOTE (DS, 2020-06-15): Keep this name for the resource file,
        // since otherwise, it'd be difficult passing this name as a parameter.
        final String javaFileName = "Problem.java";

        final ZipOutputStream zio = new ZipOutputStream(new FileOutputStream(file));

        final String proofFileName = file.getName().replaceAll(".zproof", ".proof");
        zio.putNextEntry(new ZipEntry(proofFileName));
        if (keyFileToUse.isPresent()) {
            final FileInputStream fio = new FileInputStream(keyFileToUse.get());
            byte[] buffer = new byte[8 * 1024];
            int len;
            while ((len = fio.read(buffer)) > 0) {
                zio.write(buffer, 0, len);
            }
            fio.close();
        } else {
            zio.write(createKeYFile().getBytes());
        }
        zio.closeEntry();

        zio.putNextEntry(new ZipEntry("src" + File.separator + javaFileName));
        zio.write(createJavaFile().getBytes());
        zio.closeEntry();

        zio.close();

        return new BundleSaveResult(file, FileSystems.getDefault().getPath(proofFileName));
    }

    private String createJavaFile() {
        final String paramsDecl = model.getProgramVariableDeclarations().stream()
                .map(decl -> String.format("%s %s", decl.getTypeName(), decl.getVarName()))
                .collect(Collectors.joining(","));

        final String programOne = KeyBridgeUtils.preprocessJavaCode(model.getProgramOne(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations());
        final String programTwo = KeyBridgeUtils.preprocessJavaCode(model.getProgramTwo(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations());
        final String context = KeyBridgeUtils.preprocessJavaCode(model.getMethodLevelContext(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations());

        return javaScaffold.replaceAll(PARAMS, paramsDecl)
                .replaceAll(BODY1, Matcher.quoteReplacement(programOne))
                .replaceAll(BODY2, Matcher.quoteReplacement(programTwo))
                .replaceAll(CONTEXT, Matcher.quoteReplacement(context));
    }

    private String createKeYFile() {
        final String functionsDecl;

        {
            final String locSetDecls = model.getAbstractLocationSets().stream()
                    .map(FunctionDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));

            final String userDefinedFuncDecls = model.getFunctionDeclarations().stream()
                    .map(FunctionDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));

            final String skolemPVAnonFuncDecls = model.getProgramVariableDeclarations().stream()
                    .map(decl -> String.format("%s _%s;", decl.getTypeName(), decl.getVarName()))
                    .collect(Collectors.joining("\n  "));

            functionsDecl = locSetDecls + (!model.getFunctionDeclarations().isEmpty() ? "\n  " : "")
                    + userDefinedFuncDecls
                    + (!model.getProgramVariableDeclarations().isEmpty() ? "\n  " : "")
                    + skolemPVAnonFuncDecls;
        }

        final String predicatesDecl = model.getPredicateDeclarations().stream()
                .map(PredicateDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));

        final String progvarsDecl = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));

        final String initVars = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::getVarName)
                .map(pv -> String.format("%s:=_%s", pv, pv)).collect(Collectors.joining("||"));

        final String params = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::getVarName).collect(Collectors.joining(","));

        final Services services = KeyBridgeUtils.dummyServices();
        populateNamespaces(model, services);

        final String javaDLPostCondRelation = createJavaDLPostCondition(KeyBridgeUtils.dummyKJT(),
                services);
        final String javaDLPreCondRelation = KeyBridgeUtils.createJavaDLPreCondition(
                model.getPreCondition(), model.getProgramVariableDeclarations(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations(), KeyBridgeUtils.dummyKJT(), services);

        return keyScaffold.replaceAll(FUNCTIONS, Matcher.quoteReplacement(functionsDecl))
                .replaceAll(PREDICATES, Matcher.quoteReplacement(predicatesDecl))
                .replaceAll(PROGRAMVARIABLES, Matcher.quoteReplacement(progvarsDecl))
                .replaceAll(INIT_VARS,
                        initVars.isEmpty() ? "" : (Matcher.quoteReplacement("{" + initVars + "}")))
                .replaceAll(PARAMS, Matcher.quoteReplacement(params))
                .replaceAll(Pattern.quote(RELATION),
                        Matcher.quoteReplacement(javaDLPostCondRelation))
                .replaceAll(Pattern.quote(PRECONDITION),
                        Matcher.quoteReplacement(javaDLPreCondRelation))
                .replaceAll(RESULT_SEQ_1, extractResultSeq(model.getRelevantVarsOne()))
                .replaceAll(RESULT_SEQ_2, extractResultSeq(model.getRelevantVarsTwo())) //
                .replaceAll(ADDITIONAL_PREMISES,
                        Matcher.quoteReplacement(KeyBridgeUtils
                                .createAdditionalPremises(model.getAbstractLocationSets())))
                .replaceAll(PROOF, Matcher.quoteReplacement(proofString.orElse("")));
    }

    private String createJavaDLPostCondition(final KeYJavaType dummyKJT, final Services services) {
        final String jmlPostCondRelation = preparedJMLPostCondition(model.getPostCondition(),
                model);
        return KeyBridgeUtils.jmlStringToJavaDLString(jmlPostCondRelation, dummyKJT, null, services);
    }

    public static String preparedJMLPostCondition(final String unpreparedJmlPostCondition,
            final AERelationalModel model) {
        String result = unpreparedJmlPostCondition
                .replaceAll(Pattern.quote(RESULT_1), KeyBridgeUtils.prefixDLforRE(RES1))
                .replaceAll(Pattern.quote(RESULT_2), KeyBridgeUtils.prefixDLforRE(RES2));

        result = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::getVarName)
                .collect(KeyBridgeUtils.DL_PREFIX_FOLD.apply(result));
        result = KeyBridgeUtils.dlPrefixRigidModelElements(model.getAbstractLocationSets(),
                model.getPredicateDeclarations(), model.getFunctionDeclarations(), result);

        return result;
    }

    private void populateNamespaces(final AERelationalModel model, final Services services) {
        final Namespace<Function> functions = services.getNamespaces().functions();

        final Sort seqSort = services.getTypeConverter().getSeqLDT().targetSort();
        functions.add(new Function(new Name(RelationalProofBundleConverter.RES1), seqSort));
        functions.add(new Function(new Name(RelationalProofBundleConverter.RES2), seqSort));

        model.getProgramVariableDeclarations().stream()
                .map(pvDecl -> new ProgramVariableDeclaration(pvDecl.getTypeName(),
                        "_" + pvDecl.getVarName()))
                .forEach(pvDecl -> pvDecl.checkAndRegisterSave(services));

        model.fillNamespacesFromModel(services);
    }

    private String extractResultSeq(List<NullarySymbolDeclaration> relevantSymbols) {
        String resultSeq = String.format("seqSingleton(value(singletonPV(%s)))", RESULT);

        final List<String> seqElems = Stream.concat( //
                Stream.of(new ProgramVariableDeclaration("", EXC)), relevantSymbols.stream())
                .map(NullarySymbolDeclaration::toSeqSingleton).collect(Collectors.toList());
        for (final String seqElem : seqElems) {
            resultSeq = String.format("seqConcat(%s,%s)", resultSeq, seqElem);
        }

        return resultSeq;
    }

    public static class BundleSaveResult {
        private final File file;
        private final Path proofPath;

        private BundleSaveResult(File file, Path proofPath) {
            this.file = file;
            this.proofPath = proofPath;
        }

        public File getFile() {
            return file;
        }

        public Path getProofPath() {
            return proofPath;
        }
    }

}
