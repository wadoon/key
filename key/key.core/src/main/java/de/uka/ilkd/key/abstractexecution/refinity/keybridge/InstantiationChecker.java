// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.keybridge;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import javax.xml.bind.JAXBException;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.IOUtil;
import org.xml.sax.SAXException;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.refinity.model.FunctionDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.PredicateDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.relational.AERelationalModel;
import de.uka.ilkd.key.abstractexecution.refinity.util.DummyKeYEnvironmentCreator;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.KeYJMLPreParser;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * @author Dominic Steinhoefel
 */
public class InstantiationChecker {
    private static final String JAVA_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/Problem.java";
    private static final String KEY_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/refinityInstantiationProblem.key";

    private static final String PRECONDITION = "<PRECONDITION>";
    private static final String INIT_VARS = "<INIT_VARS>";
    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String BODY = "<BODY>";
    private static final String CONTEXT = "<CONTEXT>";
    private static final String PARAMS = "<PARAMS>";
    private static final String ADDITIONAL_PREMISES = "<ADDITIONAL_PREMISES>";
    private static final String PROOF = "<PROOF>";

    private final String javaScaffold;
    private final String keyScaffold;
//    private final Optional<File> keyFileToUse;
    private final Optional<String> proofString;

    private final AEInstantiationModel model;

    public InstantiationChecker(final AEInstantiationModel instModel) throws IOException {
        this.model = instModel;

        this.proofString = Optional.empty();
//        this.keyFileToUse = Optional.empty();

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

    // TODO:
    // 1) Parse abstract program
    // 2) Get list of APEs
    // 3) Create proof obligations for APE insts (first, frame & footprint)
    // (need symbol declarations of original model)
    //
    // APE inst: number of occ. -> program

    /**
     * Returns a list of APEs from the {@link AEInstantiationModel}.
     * 
     * @return List of retrieved APEs.
     * @throws UnsuccessfulAPERetrievalException if something went wrong.
     */
    public List<APERetrievalResult> retrieveAPEs() {
        Path tmpDir;
        try {
            tmpDir = Files.createTempDirectory("AEInstCheckerTmp_");
        } catch (IOException e) {
            throw new UnsuccessfulAPERetrievalException("Could not create temporary directory", e);
        }
        tmpDir.toFile().deleteOnExit();

        final String keyFileName = "problem.key";
        final String javaSrcDirName = "src";
        final String javaFileName = "Problem.java";

        final Path keyFile = tmpDir.resolve(keyFileName);
        final Path javaSrcDir = tmpDir.resolve(javaSrcDirName);

        try {
            Files.write(keyFile, createKeYFile().getBytes());
            Files.createDirectory(javaSrcDir);
            Files.write(javaSrcDir.resolve(javaFileName), createJavaFile().getBytes());
        } catch (IOException e) {
            throw new UnsuccessfulAPERetrievalException(
                    "Could not write KeY problem file for retrieval", e);
        }

        KeYEnvironment<?> env;
        try {
            env = KeYEnvironment.load(JavaProfile.getDefaultInstance(), keyFile.toFile(),
                    Collections.emptyList(), null, Collections.emptyList(), false);
        } catch (ProblemLoaderException e) {
            throw new UnsuccessfulAPERetrievalException("Could not load KeY problem", e);
        }

        final int maxRuleApps = 80;
        final Proof proof = env.getLoadedProof();

        final ProofStarter starter = new ProofStarter(false);
        starter.init(proof);
        starter.setMaxRuleApplications(maxRuleApps);
        starter.start();

        if (proof.closed()) {
            // Proof should still be open: Otherwise, we cannot retrieve the
            // goal-local specification repository.
            throw new UnsuccessfulAPERetrievalException("Proof should be open, but is closed.");
        }

        Node currNode = proof.root();
        while (currNode.getAppliedRuleApp() != null
                && !currNode.getAppliedRuleApp().rule().name().toString().equals("methodBodyExpand")
                && currNode.childrenCount() == 1) {
            currNode = currNode.child(0);
        }

        if (!currNode.getAppliedRuleApp().rule().name().toString().equals("methodBodyExpand")) {
            throw new UnsuccessfulAPERetrievalException(
                    "Could not find methodBodyExpand application");
        }

        currNode = currNode.child(0);

        final Term formulaWithJavaBlock = //
                currNode.sequent().succedent().asList().reverse().head().formula();

        final JavaBlock javaBlock = TermBuilder.goBelowUpdates(formulaWithJavaBlock).javaBlock();

        if (javaBlock.isEmpty()) {
            throw new UnsuccessfulAPERetrievalException(
                    "Found an empty JavaBlock, probably wrong assumptions about proof structure");
        }

        final CollectAPEVisitor visitor = new CollectAPEVisitor(javaBlock.program(),
                proof.openGoals().head().getLocalSpecificationRepository(), proof.getServices());
        visitor.start();

        return visitor.getResult();
    }

    /**
     * Returns a list of APEs from either the first or second program of an
     * {@link AERelationalModel}.
     * 
     * @param relModel The {@link AERelationalModel} from which to return the APEs.
     * @param firstProgram True iff APEs should be retrieved from the first program.
     * @return A list of APEs.
     * @throws UnsuccessfulAPERetrievalException if something went wrong.
     */
    public static List<APERetrievalResult> retrieveAPEs(final AERelationalModel relModel,
            boolean firstProgram) {
        try {
            return new InstantiationChecker(
                    AEInstantiationModel.fromRelationalModel(relModel, firstProgram))
                            .retrieveAPEs();
        } catch (IOException e) {
            throw new UnsuccessfulAPERetrievalException(e);
        }
    }

    private String createJavaFile() {
        final String paramsDecl = model.getProgramVariableDeclarations().stream()
                .map(decl -> String.format("%s %s", decl.getTypeName(), decl.getVarName()))
                .collect(Collectors.joining(","));

        final String program = KeyBridgeUtils.preprocessJavaCode(model.getProgram(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations());
        final String context = KeyBridgeUtils.preprocessJavaCode(model.getMethodLevelContext(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations());

        return javaScaffold.replaceAll(PARAMS, paramsDecl)
                .replaceAll(BODY, Matcher.quoteReplacement(program))
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

        final DummyKeYEnvironmentCreator envCreator = new DummyKeYEnvironmentCreator();
        try {
            envCreator.initialize();
        } catch (ProblemLoaderException | IOException e) {
            throw new RuntimeException(
                    "Could not initialize dummy services, message: " + e.getMessage());
        }
        final Services services = envCreator.getDummyServices().get();
        populateNamespaces(model, services);

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
                .replaceAll(Pattern.quote(PRECONDITION),
                        Matcher.quoteReplacement(javaDLPreCondRelation))
                .replaceAll(ADDITIONAL_PREMISES,
                        Matcher.quoteReplacement(KeyBridgeUtils
                                .createAdditionalPremises(model.getAbstractLocationSets())))
                .replaceAll(PROOF, Matcher.quoteReplacement(proofString.orElse("")));
    }

    private void populateNamespaces(final AEInstantiationModel model, final Services services) {
        model.getProgramVariableDeclarations().stream()
                .map(pvDecl -> new ProgramVariableDeclaration(pvDecl.getTypeName(),
                        "_" + pvDecl.getVarName()))
                .forEach(pvDecl -> pvDecl.checkAndRegister(services));

        model.fillNamespacesFromModel(services);
    }

    private static class CollectAPEVisitor extends JavaASTVisitor {
        private final List<APERetrievalResult> result = new ArrayList<>();

        public CollectAPEVisitor(ProgramElement root,
                GoalLocalSpecificationRepository localSpecRepo, Services services) {
            super(root, localSpecRepo, services);
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if (node instanceof AbstractProgramElement) {
                final AbstractProgramElement ape = (AbstractProgramElement) node;

                List<TextualJMLConstruct> jmlConstructs;
                try {
                    jmlConstructs = Arrays
                            .stream(parseMethodLevelComments(ape.getComments(), "DummyProblemFile"))
                            .collect(Collectors.toList());
                } catch (SLTranslationException e) {
                    throw new RuntimeException("Could not parse APE comments", e);
                }

                result.add(new APERetrievalResult(ape, jmlConstructs));
            }
        }

        public List<APERetrievalResult> getResult() {
            return result;
        }
    }

    // Copied from JMLSpecFactory
    private static TextualJMLConstruct[] parseMethodLevelComments(final Comment[] comments,
            final String fileName) throws SLTranslationException {
        if (comments.length == 0) {
            return new TextualJMLConstruct[0];
        }
        final String concatenatedComment = Arrays.stream(comments).map(Comment::toSource)
                .collect(Collectors.joining("\n"));
        final Position position = comments[0].getStartPosition();
        final KeYJMLPreParser preParser = new KeYJMLPreParser(concatenatedComment, fileName,
                position);
        final ImmutableList<TextualJMLConstruct> constructs = preParser.parseMethodlevelComment();
        //        warnings = warnings.union(preParser.getWarnings());
        return constructs.toArray(new TextualJMLConstruct[constructs.size()]);
    }

    @SuppressWarnings("unused")
    private static class APERetrievalResult {
        private final int line;
        private final AbstractProgramElement ape;
        private final List<TextualJMLConstruct> jmlConstructs;

        public APERetrievalResult(final AbstractProgramElement ape,
                final List<TextualJMLConstruct> jmlConstructs) {
            this.ape = ape;
            this.jmlConstructs = jmlConstructs;
            // There's a shift of 3 lines in the dummy Java file.
            this.line = ape.getStartPosition().getLine() - 3;
        }

        public AbstractProgramElement getApe() {
            return ape;
        }

        public List<TextualJMLConstruct> getJMLConstructs() {
            return jmlConstructs;
        }

        public int getLine() {
            return line;
        }
    }

    @SuppressWarnings("unused")
    private static class UnsuccessfulAPERetrievalException extends RuntimeException {
        private static final long serialVersionUID = 1L;

        private final static String MESSAGE_PREFIX = "Could not retrieve APEs from program";
        private final static String MESSAGE_SEP = ", message: ";

        public UnsuccessfulAPERetrievalException() {
            super(MESSAGE_PREFIX);
        }

        public UnsuccessfulAPERetrievalException(String message, Throwable cause,
                boolean enableSuppression, boolean writableStackTrace) {
            super(MESSAGE_PREFIX + MESSAGE_SEP + message, cause, enableSuppression,
                    writableStackTrace);
        }

        public UnsuccessfulAPERetrievalException(String message, Throwable cause) {
            super(MESSAGE_PREFIX + MESSAGE_SEP + message, cause);
        }

        public UnsuccessfulAPERetrievalException(String message) {
            super(MESSAGE_PREFIX + MESSAGE_SEP + message);
        }

        public UnsuccessfulAPERetrievalException(Throwable cause) {
            super(MESSAGE_PREFIX, cause);
        }
    }

    /////////////////// Test Code ///////////////////

    public static void main(String[] args) throws JAXBException, SAXException, IOException,
            ProblemLoaderException, SLTranslationException {
        final Path testFile = Paths.get(
                "/home/dscheurer/key-workspace/GIT/key/key/key.ui/examples/abstract_execution/SlideStatements/Correct/slideStatements.aer");
        final AERelationalModel relModel = //
                AERelationalModel.fromXml(
                        Files.readAllLines(testFile).stream().collect(Collectors.joining("\n")));

        int i = 1;
        for (final APERetrievalResult result : InstantiationChecker.retrieveAPEs(relModel, false)) {
            System.out.printf("APE %d (line %d):%n", i++, result.getLine());
            //            System.out.println(Arrays.stream(result.ape.getComments()).map(Comment::toSource)
            //                    .collect(Collectors.joining("\n")));
            System.out.println(Arrays.toString(
                    parseMethodLevelComments(result.ape.getComments(), "DummyProblemFile")));
            System.out.println(result.ape.toString());
            System.out.println();
        }
    }
}
