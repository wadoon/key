// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.model;

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

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.abstractexecution.refinity.util.DummyKeYEnvironmentCreator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.JMLTranslator;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * Converts an AE Relational Model to a KeY proof bundle.
 * 
 * @author Dominic Steinhoefel
 */
public class ProofBundleConverter {
    private static final String JAVA_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/Problem.java";
    private static final String KEY_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/problem.key";

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

    // Special Keywords
    public static final String RESULT_1 = "\\result_1";
    public static final String RESULT_2 = "\\result_2";
    public static final String RES1 = "_res1";
    public static final String RES2 = "_res2";
    public static final String RESULT = "_result";
    public static final String EXC = "_exc";

    private final AERelationalModel model;
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
    public ProofBundleConverter(AERelationalModel model) throws IOException, IllegalStateException {
        this(model, null);
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
    public ProofBundleConverter(AERelationalModel model, File keyFileToUse)
            throws IOException, IllegalStateException {
        this.model = model;
        this.keyFileToUse = Optional.ofNullable(keyFileToUse);

        final InputStream javaScaffoldIS = ProofBundleConverter.class
                .getResourceAsStream(JAVA_PROBLEM_FILE_SCAFFOLD);
        final InputStream keyScaffoldIS = ProofBundleConverter.class
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
    public BundleSaveResult save(File file) throws IOException {
        assert file.getName().endsWith(".zproof");

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

        zio.putNextEntry(new ZipEntry("src" + File.separator + "Problem.java"));
        zio.write(createJavaFile().getBytes());
        zio.closeEntry();

        zio.close();

        return new BundleSaveResult(file, FileSystems.getDefault().getPath(proofFileName));
    }

    private String createJavaFile() {
        final String paramsDecl = model.getProgramVariableDeclarations().stream()
                .map(decl -> String.format("%s %s", decl.getTypeName(), decl.getVarName()))
                .collect(Collectors.joining(","));

        final String programOne = escapeDL(model.getProgramOne()).replaceAll("\n", "\n        ");
        final String programTwo = escapeDL(model.getProgramTwo()).replaceAll("\n", "\n        ");
        final String context = escapeDL(model.getMethodLevelContext()).replaceAll("\n", "\n    ");

        return javaScaffold.replaceAll(PARAMS, paramsDecl)
                .replaceAll(BODY1, Matcher.quoteReplacement(programOne))
                .replaceAll(BODY2, Matcher.quoteReplacement(programTwo))
                .replaceAll(CONTEXT, Matcher.quoteReplacement(context));
    }

    public String escapeDL(String prog) {
        for (final AbstractLocsetDeclaration locSet : model.getAbstractLocationSets()) {
            prog = prog.replaceAll("\\b" + locSet + "\\b",
                    Matcher.quoteReplacement("\\dl_" + locSet));
        }

        for (final PredicateDeclaration predDecl : model.getPredicateDeclarations()) {
            prog = prog.replaceAll("\\b" + predDecl.getPredName() + "\\b",
                    Matcher.quoteReplacement("\\dl_" + predDecl.getPredName()));
        }

        for (final FunctionDeclaration funcDecl : model.getFunctionDeclarations()) {
            prog = prog.replaceAll("\\b" + funcDecl.getFuncName() + "\\b",
                    Matcher.quoteReplacement("\\dl_" + funcDecl.getFuncName()));
        }

        return prog;
    }

    private String createKeYFile() {
        final String functionsDecl;

        {
            final String locSetDecls = model.getAbstractLocationSets().stream()
                    .map(str -> String.format("\\unique LocSet %s;", str))
                    .collect(Collectors.joining("\n  "));
            final String userDefinedFuncDecls = model.getFunctionDeclarations().stream()
                    .map(decl -> String.format("%s %s%s;", decl.getResultSortName(),
                            decl.getFuncName(),
                            decl.getArgSorts().isEmpty() ? ""
                                    : ("(" + decl.getArgSorts().stream()
                                            .collect(Collectors.joining(",")) + ")")))
                    .collect(Collectors.joining("\n  "));
            final String skolemPVAnonFuncDecls = model.getProgramVariableDeclarations().stream()
                    .map(decl -> String.format("%s _%s;", decl.getTypeName(), decl.getVarName()))
                    .collect(Collectors.joining("\n  "));

            functionsDecl = locSetDecls + (!model.getFunctionDeclarations().isEmpty() ? "\n  " : "")
                    + userDefinedFuncDecls
                    + (!model.getProgramVariableDeclarations().isEmpty() ? "\n  " : "")
                    + skolemPVAnonFuncDecls;
        }

        final String predicatesDecl = model.getPredicateDeclarations().stream()
                .map(decl -> String.format("%s%s;", decl.getPredName(),
                        decl.getArgSorts().isEmpty() ? ""
                                : ("(" + decl.getArgSorts().stream()
                                        .collect(Collectors.joining(",")) + ")")))
                .collect(Collectors.joining("\n  "));

        final String progvarsDecl = model.getProgramVariableDeclarations().stream()
                .map(decl -> String.format("%s %s;", decl.getTypeName(), decl.getVarName()))
                .collect(Collectors.joining("\n  "));

        final String initVars = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::getVarName)
                .map(pv -> String.format("%s:=_%s", pv, pv)).collect(Collectors.joining("||"));

        final String params = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::getVarName).collect(Collectors.joining(","));

        final DummyKeYEnvironmentCreator envCreator = new DummyKeYEnvironmentCreator();
        try {
            envCreator.initialize();
        } catch (ProblemLoaderException | IOException e) {
            throw new RuntimeException(
                    "Could not initialize dummy services, message: " + e.getMessage());
        }
        final Services services = envCreator.getDummyServices().get();
        populateNamespaces(model, services);

        final String javaDLPostCondRelation = createJavaDLPostCondition(
                envCreator.getDummyKjt().get(), services);
        final String javaDLPreCondRelation = createJavaDLPreCondition(
                envCreator.getDummyKjt().get(), services);

        return keyScaffold.replaceAll(FUNCTIONS, Matcher.quoteReplacement(functionsDecl))
                .replaceAll(PREDICATES, Matcher.quoteReplacement(predicatesDecl))
                .replaceAll(PROGRAMVARIABLES, Matcher.quoteReplacement(progvarsDecl))
                .replaceAll(INIT_VARS,
                        initVars.isEmpty() ? "" : (Matcher.quoteReplacement("||" + initVars)))
                .replaceAll(PARAMS, Matcher.quoteReplacement(params))
                .replaceAll(Pattern.quote(RELATION), Matcher.quoteReplacement(javaDLPostCondRelation))
                .replaceAll(Pattern.quote(PRECONDITION), Matcher.quoteReplacement(javaDLPreCondRelation))
                .replaceAll(RESULT_SEQ_1, extractResultSeq(model.getRelevantVarsOne()))
                .replaceAll(RESULT_SEQ_2, extractResultSeq(model.getRelevantVarsTwo())) //
                .replaceAll(ADDITIONAL_PREMISES,
                        Matcher.quoteReplacement(createAdditionalPremises()));
    }

    private String createJavaDLPostCondition(final KeYJavaType dummyKJT, final Services services) {
        final String jmlPostCondRelation = preparedJMLPostCondition(model.getPostCondition(),
                model);
        return jmlStringToJavaDL(jmlPostCondRelation, dummyKJT, services);
    }

    private String createJavaDLPreCondition(final KeYJavaType dummyKJT, final Services services) {
        final String preCondition = model.getPreCondition();
        if (preCondition.trim().isEmpty()) {
            // Precondition is optional
            return "true";
        }

        final String jmlPreCondRelation = preparedJMLPreCondition(preCondition, model);
        return jmlStringToJavaDL(jmlPreCondRelation, dummyKJT, services);
    }

    private static String jmlStringToJavaDL(String jmlString, final KeYJavaType dummyKJT,
            final Services services) {
        try {
            Term parsed = translateJML(jmlString, dummyKJT, services);
            parsed = removeLabels(parsed, services);
            return LogicPrinter.quickPrintTerm(parsed, services);
        } catch (Exception e) {
            throw new RuntimeException("Could not parse JML formula, message: " + e.getMessage(),
                    e);
        }
    }

    private static Term translateJML(String jmlPostCondRelation, final KeYJavaType dummyKJT,
            final Services services) throws SLTranslationException {
        return JMLTranslator.translate(new PositionedString(jmlPostCondRelation), dummyKJT, null,
                null, null, null, null, null, Term.class, services);
    }

    private static Term removeLabels(final Term term, final Services services) {
        final TermFactory tf = services.getTermFactory();
        return tf.createTerm(term.op(),
                new ImmutableArray<>(term.subs().stream().map(t -> removeLabels(t, services))
                        .collect(Collectors.toList())),
                term.boundVars(), term.javaBlock(), new ImmutableArray<>());
    }

    public static String preparedJMLPostCondition(final String unpreparedJmlPostCondition,
            final AERelationalModel model) {
        String result = unpreparedJmlPostCondition
                .replaceAll(Pattern.quote(RESULT_1), prefixDLforRE(RES1))
                .replaceAll(Pattern.quote(RESULT_2), prefixDLforRE(RES2));

        return preparedJMLPreCondition(result, model);
    }

    public static String preparedJMLPreCondition(final String unpreparedJmlPreCondition,
            final AERelationalModel model) {
        String result = unpreparedJmlPreCondition;
        for (final FunctionDeclaration decl : model.getFunctionDeclarations()) {
            result = prefixOccurrencesWithDL(result, decl.getFuncName());
        }

        for (final PredicateDeclaration decl : model.getPredicateDeclarations()) {
            result = prefixOccurrencesWithDL(result, decl.getPredName());
        }

        return result;
    }

    private static String prefixOccurrencesWithDL(String in, String toPrefix) {
        return in.replaceAll("\\b" + Pattern.quote(toPrefix) + "\\b", prefixDLforRE(toPrefix));
    }

    private static String prefixDLforRE(String str) {
        return Matcher.quoteReplacement(String.format("\\dl_%s", str));
    }

    private void populateNamespaces(final AERelationalModel model, final Services services) {
        final Namespace<Function> functions = services.getNamespaces().functions();

        final Sort seqSort = services.getTypeConverter().getSeqLDT().targetSort();
        functions.add(new Function(new Name(ProofBundleConverter.RES1), seqSort));
        functions.add(new Function(new Name(ProofBundleConverter.RES2), seqSort));

        model.fillNamespacesFromModel(services);
    }

    private String createAdditionalPremises() {
        if (model.getAbstractLocationSets().isEmpty()) {
            return "";
        }

        final StringBuilder sb = new StringBuilder();

        for (final AbstractLocsetDeclaration decl : model.getAbstractLocationSets()) {
            sb.append("\n     & ") //
                    .append("disjoint(singletonPV(") //
                    .append(RESULT) //
                    .append("),") //
                    .append(decl.getLocsetName()) //
                    .append(")");
            sb.append("\n     & ") //
                    .append("disjoint(singletonPV(") //
                    .append(EXC) //
                    .append("),") //
                    .append(decl.getLocsetName()) //
                    .append(")");

        }

        return sb.toString();
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
