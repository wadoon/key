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
package de.uka.ilkd.key.abstractexecution.relational.model;

import java.io.BufferedInputStream;
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
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

/**
 * Converts an AE Relational Model to a KeY proof bundle.
 * 
 * @author Dominic Steinhoefel
 */
public class ProofBundleConverter {
    private static final String JAVA_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/abstractexecution/relational/Problem.java";
    private static final String KEY_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/abstractexecution/relational/problem.key";

    private static final String RELATION = "<RELATION>";
    private static final String INIT_VARS = "<INIT_VARS>";
    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String BODY2 = "<BODY2>";
    private static final String BODY1 = "<BODY1>";
    private static final String PARAMS = "<PARAMS>";
    private static final String RESULT_SEQ_1 = "<RESULT_SEQ_1>";
    private static final String RESULT_SEQ_2 = "<RESULT_SEQ_2>";

    // Special Keywords
    public static final String RESULT_1 = "\\result_1";
    public static final String RESULT_2 = "\\result_2";
    public static final String RES1 = "_res1";
    public static final String RES2 = "_res2";
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

        javaScaffold = inputStreamToString(javaScaffoldIS);
        keyScaffold = inputStreamToString(keyScaffoldIS);
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

        final String programOne = processProgram(model.getProgramOne());
        final String programTwo = processProgram(model.getProgramTwo());

        return javaScaffold.replaceAll(PARAMS, paramsDecl)
                .replaceAll(BODY1, Matcher.quoteReplacement(programOne))
                .replaceAll(BODY2, Matcher.quoteReplacement(programTwo));
    }

    private String processProgram(String prog) {
        for (final AbstractLocsetDeclaration locSet : model.getAbstractLocationSets()) {
            prog = prog.replaceAll("\\b" + locSet + "\\b",
                    Matcher.quoteReplacement("\\dl_" + locSet));
        }

        for (final PredicateDeclaration predDecl : model.getPredicateDeclarations()) {
            prog = prog.replaceAll("\\b" + predDecl.getPredName() + "\\b",
                    Matcher.quoteReplacement("\\dl_" + predDecl.getPredName()));
        }

        return prog.replaceAll("\n", "\n        ");
    }

    private String createKeYFile() {
        final String functionsDecl = model.getAbstractLocationSets().stream()
                .map(str -> String.format("\\unique LocSet %s;", str))
                .collect(Collectors.joining("\n  "))
                + (!model.getProgramVariableDeclarations().isEmpty() ? "\n  " : "")
                + model.getProgramVariableDeclarations().stream().map(
                        decl -> String.format("%s _%s;", decl.getTypeName(), decl.getVarName()))
                        .collect(Collectors.joining("\n  "));

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

        final String postCondRelation = Matcher.quoteReplacement(model.getPostCondition())
                .replaceAll(Pattern.quote(RESULT_1), RES1)
                .replaceAll(Pattern.quote(RESULT_2), RES2);

        return keyScaffold.replaceAll(FUNCTIONS, Matcher.quoteReplacement(functionsDecl))
                .replaceAll(PREDICATES, Matcher.quoteReplacement(predicatesDecl))
                .replaceAll(PROGRAMVARIABLES, Matcher.quoteReplacement(progvarsDecl))
                .replaceAll(INIT_VARS,
                        initVars.isEmpty() ? "" : (Matcher.quoteReplacement(initVars)))
                .replaceAll(PARAMS, Matcher.quoteReplacement(params))
                .replaceAll(RELATION, postCondRelation)
                .replaceAll(RESULT_SEQ_1, extractResultSeq(model.getRelevantVarsOne()))
                .replaceAll(RESULT_SEQ_2, extractResultSeq(model.getRelevantVarsTwo()));
    }

    private String extractResultSeq(List<NullarySymbolDeclaration> relevantSymbols) {
        String resultSeq = "seqSingleton(value(singletonPV(_exc)))";

        final List<String> seqElems = relevantSymbols.stream()
                .map(NullarySymbolDeclaration::toSeqSingleton).collect(Collectors.toList());
        for (final String seqElem : seqElems) {
            resultSeq = String.format("seqConcat(%s,%s)", resultSeq, seqElem);
        }

        return resultSeq;
    }

    private static String inputStreamToString(InputStream is) throws IOException {
        final StringBuilder sb = new StringBuilder();
        final BufferedInputStream in = new BufferedInputStream(is);
        byte[] contents = new byte[1024];

        int bytesRead = 0;
        while ((bytesRead = in.read(contents)) != -1) {
            sb.append(new String(contents, 0, bytesRead));
        }

        return sb.toString();
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
