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
package de.uka.ilkd.key.gui.abstractexecution.relational;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.util.regex.Matcher;
import java.util.stream.Collectors;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import de.uka.ilkd.key.gui.abstractexecution.relational.model.AERelationalModel;
import de.uka.ilkd.key.gui.abstractexecution.relational.model.ProgramVariableDeclaration;

/**
 * @author Dominic Steinhoefel
 */
public class ProofBundleConverter {
    private static final String POST = "<POST>";
    private static final String INIT_VARS = "<INIT_VARS>";
    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String BODY2 = "<BODY2>";
    private static final String BODY1 = "<BODY1>";
    private static final String PARAMS = "<PARAMS>";

    private final AERelationalModel model;
    private final String javaScaffold;
    private final String keyScaffold;

    public ProofBundleConverter(AERelationalModel model, String javaScaffold, String keyScaffold) {
        this.model = model;
        this.javaScaffold = javaScaffold;
        this.keyScaffold = keyScaffold;
    }

    private String createJavaFile() {
        final String paramsDecl = model.getProgramVariableDeclarations().stream()
                .map(decl -> String.format("%s %s", decl.getTypeName(), decl.getVarName()))
                .collect(Collectors.joining(","));
        return javaScaffold.replaceAll(PARAMS, paramsDecl)
                .replaceAll(BODY1,
                        Matcher.quoteReplacement(
                                model.getProgramOne().replaceAll("\n", "\n        ")))
                .replaceAll(BODY2, Matcher
                        .quoteReplacement(model.getProgramTwo().replaceAll("\n", "\n        ")));
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

        return keyScaffold.replaceAll(FUNCTIONS, Matcher.quoteReplacement(functionsDecl))
                .replaceAll(PREDICATES, Matcher.quoteReplacement(predicatesDecl))
                .replaceAll(PROGRAMVARIABLES, Matcher.quoteReplacement(progvarsDecl))
                .replaceAll(INIT_VARS,
                        initVars.isEmpty() ? "" : ("{" + Matcher.quoteReplacement(initVars) + "}"))
                .replaceAll(PARAMS, Matcher.quoteReplacement(params))
                .replaceAll(POST, model.getPostCondition());
    }

    public BundleSaveResult save(File file) throws IOException {
        assert file.getName().endsWith(".zproof");

        final ZipOutputStream zio = new ZipOutputStream(new FileOutputStream(file));

        final String proofFileName = file.getName().replaceAll(".zproof", ".proof");
        zio.putNextEntry(new ZipEntry(proofFileName));
        zio.write(createKeYFile().getBytes());
        zio.closeEntry();

        zio.putNextEntry(new ZipEntry("src" + File.separator + "Problem.java"));
        zio.write(createJavaFile().getBytes());
        zio.closeEntry();

        zio.close();

        return new BundleSaveResult(file, FileSystems.getDefault().getPath(proofFileName));
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
