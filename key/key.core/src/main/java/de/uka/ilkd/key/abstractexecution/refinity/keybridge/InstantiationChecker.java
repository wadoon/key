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

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import javax.xml.bind.JAXBException;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.IOUtil;
import org.xml.sax.SAXException;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.refinity.model.FunctionDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.PredicateDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.FunctionInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.PredicateInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.model.relational.AERelationalModel;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.KeYJMLPreParser;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.MiscTools;
import recoder.ModelException;

/**
 * @author Dominic Steinhoefel
 */
public class InstantiationChecker {
    private static final String JAVA_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/Problem.java";

    private static final String APE_RETRIEVAL_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/programRetrievalProblem.key";

    private static final String FRAME_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/frameProblem.key";

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
    private static final String SYMINSTS = "<SYMINSTS>";
    private static final String ASSIGNABLES = "<ASSIGNABLES>";
    private static final String AT_PRES = "<AT_PRES>";
    private static final String PV_AT_PRE_POSTS = "<PV_AT_PRE_POSTS>";

    private final String javaScaffold;

    private final String keyRetrieveAPEsScaffold;

    private final String keyProveFrameScaffold;

//    private final Optional<File> keyFileToUse;
    private final Optional<String> proofString;

    private final AEInstantiationModel model;

    final Services services;

    /** A cached list of APEs in the model to save time. */
    private Optional<List<APERetrievalResult>> apes = Optional.empty();

    public InstantiationChecker(final AEInstantiationModel instModel) throws IOException {
        this.model = instModel;

        services = KeyBridgeUtils.dummyServices();
        populateNamespaces(model, services);

        this.proofString = Optional.empty();
//        this.keyFileToUse = Optional.empty();

        final InputStream javaScaffoldIS = RelationalProofBundleConverter.class
                .getResourceAsStream(JAVA_PROBLEM_FILE_SCAFFOLD);
        final InputStream keyScaffoldIS = RelationalProofBundleConverter.class
                .getResourceAsStream(APE_RETRIEVAL_PROBLEM_FILE_SCAFFOLD);
        if (javaScaffoldIS == null || keyScaffoldIS == null) {
            throw new IllegalStateException("Could not load required resource files.");
        }

        javaScaffold = IOUtil.readFrom(javaScaffoldIS);
        keyRetrieveAPEsScaffold = IOUtil.readFrom(keyScaffoldIS);

        final InputStream keyFrameProblemIS = RelationalProofBundleConverter.class
                .getResourceAsStream(FRAME_PROBLEM_FILE_SCAFFOLD);
        if (keyFrameProblemIS == null) {
            throw new IllegalStateException("Could not load required resource files.");
        }

        keyProveFrameScaffold = IOUtil.readFrom(keyFrameProblemIS);
    }

    ////////////// Public Static Functions ////////////// 

    ////////////// Public Member Functions //////////////

    public ProofResult proveInstantiation(final boolean printOutput) {
        this.printOutput = printOutput;
        /* non-final */ ProofResult result = ProofResult.EMPTY;

        ///////// Frame Condition

        {
            println("Proving Frame Condition(s)...");
            final ProofResult frameProofResults = proveFrameInsts();
            printIndividualProofResultStats(frameProofResults);
            result = result.merge(frameProofResults);
        }

        ///////// Has-To

        {
            println("Proving hasTo Condition(s)...");
            final ProofResult hasToProofResults = proveHasToInsts();
            printIndividualProofResultStats(hasToProofResults);
            result = result.merge(hasToProofResults);
        }

        ///////// Footprint Specification

        ///////// Termination

        ///////// Normal Completion Spec

        ///////// Completion Due to Return Spec

        ///////// Completion Due to Thrown Exception Spec

        ///////// Completion Due to Break Spec

        ///////// Completion Due to Continue Spec

        ///////// NOTE (DS, 2020-07-16): Labeled continue / break omitted, spec case not yet supported.

        ///////// Constraints (assumptions) satisfied

        ///////// Consistent instantiations of APEs w/ same IDs

        return result;
    }

    /**
     * Returns a list of APEs from the {@link AEInstantiationModel}.
     * 
     * @return List of retrieved APEs.
     * @throws UnsuccessfulAPERetrievalException if something went wrong. If the
     * reason is an {@link SLTranslationException} (i.e., problem in the JML specs),
     * the cause of the thrown exception object is the
     * {@link SLTranslationException}. If the reason is an {@link ModelException}
     * (i.e., problem in the Java code), the cause of the thrown exception object is
     * the {@link ModelException}.
     */
    public List<APERetrievalResult> retrieveAPEs() {
        if (apes.isPresent()) {
            return apes.get();
        }

        final RetrieveProgramResult retrProgRes = retrieveProgram(model.getProgram());

        final CollectAPEVisitor visitor = new CollectAPEVisitor(retrProgRes.getProgram(),
                retrProgRes.getLocalSpecRepo(), retrProgRes.getServices());
        visitor.start();

        final List<APERetrievalResult> result = visitor.getResult();

        // Cache result 
        this.apes = Optional.of(result);

        return result;
    }

    /**
     * Creates the proof used to retrieve APEs from the code body.
     * 
     * @param maxNumSteps Maximum number of applied steps.
     * @param program The code of the program which to parse / analyze.
     * @return The created proof.
     * @throws UnsuccessfulAPERetrievalException if something went wrong. If the
     * reason is an {@link SLTranslationException} (i.e., problem in the JML specs),
     * the cause of the thrown exception object is the
     * {@link SLTranslationException}. If the reason is an {@link ModelException}
     * (i.e., problem in the Java code), the cause of the thrown exception object is
     * the {@link ModelException}.
     */
    public Proof createRetrievalProof(final int maxNumSteps, final String program)
            throws UnsuccessfulAPERetrievalException {
        final String keyFileContent = createRetrievalKeYFile();
        final String javaFileContent = createJavaFile(program);

        final Proof proof;
        try {
            proof = KeyBridgeUtils.createProofAndRun(keyFileContent, javaFileContent, maxNumSteps);
        } catch (RuntimeException rte) {
            throw new UnsuccessfulAPERetrievalException(rte.getMessage(), rte.getCause());
        }
        assert !proof.closed();
        return proof;
    }

    ////////////// Private Member Functions //////////////

    private void printIndividualProofResultStats(final ProofResult proofResult) {
        if (printOutput) {
            if (proofResult.isSuccess()) {
                println("Success.");
            } else {
                println("Could not prove frame condition(s).");
                println("Failed proof(s):");
                proofResult.getProofs().stream().filter(p -> !p.closed()).map(Proof::getProofFile)
                        .map(File::toString).forEach(this::println);
            }
        }
    }

    /**
     * Proves the frame conditions for all instantiated APEs.
     * 
     * @return The proof result.
     */
    private ProofResult proveFrameInsts() {
        return model.getApeInstantiations().stream().map(this::proveFrameInst)
                .collect(ProofResult.REDUCER);
    }

    /**
     * Proves the frame conditions for all instantiated APEs.
     * 
     * @return The proof result.
     */
    private ProofResult proveHasToInsts() {
        return model.getApeInstantiations().stream().map(this::proveHasToInst)
                .collect(ProofResult.REDUCER);
    }

    /**
     * Attempts to prove that the given instantiation satisfies the hasTo condition
     * of the APE to instantiate.
     * 
     * @param inst The {@link APEInstantiation}
     * @return A {@link ProofResult} for the frame problem.
     */
    private ProofResult proveHasToInst(APEInstantiation inst) {
        final TermBuilder tb = services.getTermBuilder();
        final Collector<Term, ?, Term> unionReducer = Collectors.reducing(tb.empty(),
                (ls1, ls2) -> tb.union(ls1, ls2));

        final RetrieveProgramResult retrProgRes = //
                retrieveProgram(inst.getInstantiation());

        final GoalLocalSpecificationRepository localSpecRepo = retrProgRes.getLocalSpecRepo();
        final ImmutableSet<ProgramVariable> outVars = MiscTools
                .getLocalOuts(retrProgRes.getProgram(), localSpecRepo, retrProgRes.getServices());

        if (outVars.isEmpty()) {
            return ProofResult.EMPTY;
        }

        final Term writtenVarsTerm = outVars.stream().map(LocationVariable.class::cast)
                .map(tb::singletonPV).collect(unionReducer);

        final Set<AbstractUpdateLoc> hasToLocs = AbstractUpdateFactory
                .abstrUpdateLocsFromUnionTerm(getAssignableTerm(inst), Optional.empty(), services)
                .stream().filter(HasToLoc.class::isInstance).map(HasToLoc.class::cast)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));

        if (hasToLocs.isEmpty()) {
            return ProofResult.EMPTY;
        }

        final Term hasToLocsTerm = hasToLocs.stream().map(loc -> loc.toTerm(services))
                .collect(unionReducer);

        final Term assumptionTerm;
        {
            try {
                assumptionTerm = KeyBridgeUtils.parseTerm(//
                        createSymInsts(), localSpecRepo, services);
            } catch (RecognitionException re) {
                throw new InvalidSyntaxException(re.getMessage(), re.getCause());
            }
        }

        final Term proofTerm = tb.imp(assumptionTerm, tb.subset(hasToLocsTerm, writtenVarsTerm));

        final Proof proof = new Proof("HasTo_Proof", proofTerm, keyFileHeader(inst),
                services.getProof().getInitConfig());

        KeyBridgeUtils.runProof(proof, 10000);

        try {
            proof.saveToFile(KeyBridgeUtils.createTmpDir().resolve("hasToProof.proof").toFile());
        } catch (IOException e) {
            throw new RuntimeException("Could not save KeY proof", e);
        }

        return new ProofResult(proof.closed(), proof);
    }

    /**
     * Attempts to prove that the given instantiation satisfies the frame condition
     * of the APE to instantiate.
     * 
     * @param inst The {@link APEInstantiation}
     * @return A {@link ProofResult} for the frame problem.
     */
    private ProofResult proveFrameInst(APEInstantiation inst) {
        final String keyFileContent = createProveFrameKeYFile(inst);
        final String javaFileContent = createJavaFile(inst.getInstantiation());

        final Proof proof;
        try {
            proof = KeyBridgeUtils.createProofAndRun(keyFileContent, javaFileContent, 10000);
        } catch (RuntimeException rte) {
            // Maybe convert to different exception class...
            throw rte;
        }

        return new ProofResult(proof.closed(), proof);
    }

    /**
     * Returns a list of APEs from the {@link AEInstantiationModel}.
     * 
     * @return List of retrieved APEs.
     * @throws UnsuccessfulAPERetrievalException if something went wrong. If the
     * reason is an {@link SLTranslationException} (i.e., problem in the JML specs),
     * the cause of the thrown exception object is the
     * {@link SLTranslationException}. If the reason is an {@link ModelException}
     * (i.e., problem in the Java code), the cause of the thrown exception object is
     * the {@link ModelException}.
     */
    private RetrieveProgramResult retrieveProgram(final String code) {
        final Proof proof = createRetrievalProof(80, code);

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

        return new RetrieveProgramResult(javaBlock.program(), proof);
    }

    private String createProveFrameKeYFile(APEInstantiation inst) {
        final String javaDLPreCondRelation = KeyBridgeUtils.createJavaDLPreCondition(
                model.getPreCondition(), model.getProgramVariableDeclarations(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations(), KeyBridgeUtils.dummyKJT(), services);

        //////////

        final String symInsts = createSymInsts();

        //////////

        final String atPres;
        final LinkedHashSet<LocationVariable> instProgVars;

        {
            final RetrieveProgramResult retrProgRes = retrieveProgram(inst.getInstantiation());
            final ProgramVariableCollector progVarCol = new ProgramVariableCollector(
                    retrProgRes.getProgram(), retrProgRes.getLocalSpecRepo(),
                    retrProgRes.getServices());
            progVarCol.start();

            final List<String> ignPVs = Arrays
                    .asList(new String[] { "_result", "_exc", "_objUnderTest" });

            instProgVars = progVarCol.result().stream()
                    .filter(lv -> !ignPVs.contains(lv.name().toString()))
                    .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
            atPres = instProgVars.stream().map(pv -> String.format("%1$s_AtPre:=%1$s", pv))
                    .collect(Collectors.joining("||"));
        }

        //////////

        final String javaDlAssignableTerm = getAssignableTermString(inst);

        //////////

        final String pvAtPrePosts;

        {
            pvAtPrePosts = instProgVars.stream().map(LocationVariable::toString)
                    .map(v -> String.format("(%1$s=%1$s_AtPre | pvElementOf(PV(%1$s), %2$s))", v,
                            javaDlAssignableTerm))
                    .collect(Collectors.joining("\n              & "));
        }

        //////////

        final String newVars;

        {
            final String newInstVars = instProgVars.stream()
                    .filter(lv -> !model.getProgramVariableDeclarations().stream()
                            .anyMatch(pvd -> pvd.getName().equals(lv.name().toString())))
                    .map(lv -> String.format("%s %s;",
                            lv.getKeYJavaType().getSort().name().toString(), lv.name().toString()))
                    .collect(Collectors.joining("\n  "));

            final String atPreVars = instProgVars.stream()
                    .map(lv -> String.format("%s %s_AtPre;",
                            lv.getKeYJavaType().getSort().name().toString(), lv.name().toString()))
                    .collect(Collectors.joining("\n  "));

            newVars = "\n  " + newInstVars + "\n  " + atPreVars;
        }

        return keyProveFrameScaffold
                .replaceAll(FUNCTIONS, Matcher.quoteReplacement(createFuncDecls()))
                .replaceAll(PREDICATES, Matcher.quoteReplacement(createPredDecls()))
                .replaceAll(PROGRAMVARIABLES,
                        Matcher.quoteReplacement(createProgvarDecls() + newVars))
                .replaceAll(PARAMS, Matcher.quoteReplacement(createParams()))
                .replaceAll(SYMINSTS, Matcher.quoteReplacement(symInsts))
                .replaceAll(AT_PRES, Matcher.quoteReplacement(atPres))
                .replaceAll(ASSIGNABLES, Matcher.quoteReplacement(javaDlAssignableTerm))
                .replaceAll(PV_AT_PRE_POSTS, pvAtPrePosts)
                .replaceAll(Pattern.quote(PRECONDITION),
                        Matcher.quoteReplacement(javaDLPreCondRelation))
                .replaceAll(ADDITIONAL_PREMISES, Matcher.quoteReplacement(
                        KeyBridgeUtils.createAdditionalPremises(model.getAbstractLocationSets())));
    }

    /**
     * @return A string representing the instantiations of symbolic functions and
     * predicates.
     */
    private String createSymInsts() {
        final String funcInsts = model.getFunctionInstantiations().stream()
                .map(FunctionInstantiation::toString).collect(Collectors.joining(" &\n  "));
        final String predInsts = model.getPredicateInstantiations().stream()
                .map(PredicateInstantiation::toString).collect(Collectors.joining(" &\n  "));
        return funcInsts.isEmpty() ? (predInsts.isEmpty() ? "true" : predInsts)
                : (predInsts.isEmpty() ? funcInsts : funcInsts + " &\n  " + predInsts);
    }

    /**
     * Returns a header for a KeY proof, including declarations of variables in the
     * instantiation.
     * 
     * @param inst The instantiation (for declaring free variables).
     * @return The header.
     */
    private String keyFileHeader(final APEInstantiation inst) {
        final LinkedHashSet<LocationVariable> instProgVars;

        {
            final RetrieveProgramResult retrProgRes = retrieveProgram(inst.getInstantiation());
            final ProgramVariableCollector progVarCol = new ProgramVariableCollector(
                    retrProgRes.getProgram(), retrProgRes.getLocalSpecRepo(),
                    retrProgRes.getServices());
            progVarCol.start();

            final List<String> ignPVs = Arrays
                    .asList(new String[] { "_result", "_exc", "_objUnderTest" });

            instProgVars = progVarCol.result().stream()
                    .filter(lv -> !ignPVs.contains(lv.name().toString()))
                    .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
        }

        //////////

        final String newVars;

        {
            final String newInstVars = instProgVars.stream()
                    .filter(lv -> !model.getProgramVariableDeclarations().stream()
                            .anyMatch(pvd -> pvd.getName().equals(lv.name().toString())))
                    .map(lv -> String.format("%s %s;",
                            lv.getKeYJavaType().getSort().name().toString(), lv.name().toString()))
                    .collect(Collectors.joining("\n  "));

            final String atPreVars = instProgVars.stream()
                    .map(lv -> String.format("%s %s_AtPre;",
                            lv.getKeYJavaType().getSort().name().toString(), lv.name().toString()))
                    .collect(Collectors.joining("\n  "));

            newVars = "\n  " + newInstVars + "\n  " + atPreVars;
        }

        return keyProveFrameScaffold
                .replaceAll(FUNCTIONS, Matcher.quoteReplacement(createFuncDecls()))
                .replaceAll(PREDICATES, Matcher.quoteReplacement(createPredDecls())).replaceAll(
                        PROGRAMVARIABLES, Matcher.quoteReplacement(createProgvarDecls() + newVars));
    }

    /**
     * Returns a String representation of the assignable term of the given
     * {@link APEInstantiation}.
     * 
     * @param inst
     * @return
     * @throws UnsuccessfulAPERetrievalException
     */
    private String getAssignableTermString(APEInstantiation inst)
            throws UnsuccessfulAPERetrievalException {
        return LogicPrinter.quickPrintTerm(getAssignableTerm(inst), services, false, false);
    }

    /**
     * Returns the assignable term of the given {@link APEInstantiation}.
     * 
     * @param inst
     * @return
     * @throws UnsuccessfulAPERetrievalException
     */
    private Term getAssignableTerm(APEInstantiation inst) throws UnsuccessfulAPERetrievalException {
        final String jmlAssignableTerm = getAssignableTerm(retrieveAPEs().stream()
                .filter(r -> r.getLine() == inst.getApeLineNumber()).findFirst()
                .orElseThrow(() -> new UnsuccessfulAPERetrievalException(
                        "Expected to find APE with line no. " + inst.getApeLineNumber()
                                + ", but did not.")));
        return KeyBridgeUtils.jmlStringToJavaDLTerm( //
                jmlAssignableTerm, KeyBridgeUtils.dummyKJT(), services);
    }

    private String getAssignableTerm(final APERetrievalResult ape) {
        return ape.jmlConstructs.stream().filter(TextualJMLSpecCase.class::isInstance)
                .map(TextualJMLSpecCase.class::cast).filter(c -> c.getBehavior() == Behavior.NONE)
                .filter(c -> c.getAssignable() != null).map(TextualJMLSpecCase::getAssignable)
                .map(ImmutableList::head).findAny().map(str -> str.text)
                .map(str -> str.replaceAll("assignable ", "")).map(str -> str.replaceAll(";", ""))
                .orElse("\\everything");
    }

    private String createJavaFile(String bodyReplacement) {
        final String paramsDecl = model.getProgramVariableDeclarations().stream()
                .map(decl -> String.format("%s %s", decl.getTypeName(), decl.getVarName()))
                .collect(Collectors.joining(","));

        final String program = KeyBridgeUtils.preprocessJavaCode(bodyReplacement,
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations());
        final String context = KeyBridgeUtils.preprocessJavaCode(model.getMethodLevelContext(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations());

        return javaScaffold.replaceAll(PARAMS, paramsDecl)
                .replaceAll(BODY, Matcher.quoteReplacement(program))
                .replaceAll(CONTEXT, Matcher.quoteReplacement(context));
    }

    private String createRetrievalKeYFile() {
        final String initVars = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::getVarName)
                .map(pv -> String.format("%s:=_%s", pv, pv)).collect(Collectors.joining("||"));

        final Services services = KeyBridgeUtils.dummyServices();
        populateNamespaces(model, services);

        final String javaDLPreCondRelation = KeyBridgeUtils.createJavaDLPreCondition(
                model.getPreCondition(), model.getProgramVariableDeclarations(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations(), KeyBridgeUtils.dummyKJT(), services);

        return keyRetrieveAPEsScaffold
                .replaceAll(FUNCTIONS, Matcher.quoteReplacement(createFuncDecls()))
                .replaceAll(PREDICATES, Matcher.quoteReplacement(createPredDecls()))
                .replaceAll(PROGRAMVARIABLES, Matcher.quoteReplacement(createProgvarDecls()))
                .replaceAll(INIT_VARS,
                        initVars.isEmpty() ? "" : (Matcher.quoteReplacement("{" + initVars + "}")))
                .replaceAll(PARAMS, Matcher.quoteReplacement(createParams()))
                .replaceAll(Pattern.quote(PRECONDITION),
                        Matcher.quoteReplacement(javaDLPreCondRelation))
                .replaceAll(ADDITIONAL_PREMISES,
                        Matcher.quoteReplacement(KeyBridgeUtils
                                .createAdditionalPremises(model.getAbstractLocationSets())))
                .replaceAll(PROOF, Matcher.quoteReplacement(proofString.orElse("")));
    }

    private String createParams() {
        final String params = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::getVarName).collect(Collectors.joining(","));
        return params;
    }

    private String createProgvarDecls() {
        final String progvarsDecl = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));
        return progvarsDecl;
    }

    private String createPredDecls() {
        final String predicatesDecl = model.getPredicateDeclarations().stream()
                .map(PredicateDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));
        return predicatesDecl;
    }

    private String createFuncDecls() {
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
        return functionsDecl;
    }

    private void populateNamespaces(final AEInstantiationModel model, final Services services) {
        model.getProgramVariableDeclarations().stream()
                .map(pvDecl -> new ProgramVariableDeclaration(pvDecl.getTypeName(),
                        "_" + pvDecl.getVarName()))
                .forEach(pvDecl -> pvDecl.checkAndRegister(services));

        model.fillNamespacesFromModel(services);
    }

    private boolean printOutput = true;

    /**
     * Prints the given string to System.out (w/ newline) if the field
     * {@link #printOutput} is set to true.
     * 
     * @param str The string to (conditionally) print.
     */
    private void println(final String str) {
        if (printOutput) {
            System.out.println(str);
        }
    }

    ////////////// Private Static Functions //////////////

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
        final KeYJMLPreParser preParser = //
                new KeYJMLPreParser(concatenatedComment, fileName, position);
        final ImmutableList<TextualJMLConstruct> constructs = preParser.parseMethodlevelComment();
        //        warnings = warnings.union(preParser.getWarnings());
        return constructs.toArray(new TextualJMLConstruct[constructs.size()]);
    }

    ////////////// Inner Classes //////////////

    public static class APERetrievalResult {
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

    /////////////////// Test Code ///////////////////

    public static void main(String[] args) throws JAXBException, SAXException, IOException,
            ProblemLoaderException, SLTranslationException {
        final Path testFile = Paths.get(
                "/home/dscheurer/key-workspace/GIT/key/key/key.ui/examples/abstract_execution/SlideStatements/Correct/slideStatements.aer");
        final AERelationalModel relModel = //
                AERelationalModel.fromXml(
                        Files.readAllLines(testFile).stream().collect(Collectors.joining("\n")));

        // There are ASs at lines 19 and 25
        final AEInstantiationModel instModel = //
                AEInstantiationModel.fromRelationalModel(relModel, true);

        for (final String newPV : new String[] { "a", "b", "d", "w", "x", "y", "z" }) {
            instModel.getProgramVariableDeclarations()
                    .add(new ProgramVariableDeclaration("int", newPV));
        }

        instModel.addFunctionInstantiation(new FunctionInstantiation(
                instModel.getAbstractLocationSets().stream()
                        .filter(decl -> decl.getFuncName().equals("frameA")).findAny().get(),
                "union(singletonPV(PV(x)), union(singletonPV(PV(y)), singletonPV(PV(z))))"));

        instModel.addFunctionInstantiation(new FunctionInstantiation(
                instModel.getAbstractLocationSets().stream()
                        .filter(decl -> decl.getFuncName().equals("footprintA")).findAny().get(),
                "union(singletonPV(PV(y)), singletonPV(PV(w)))"));

        instModel.addApeInstantiation(new APEInstantiation(19, "x = y++; z = w;"));
        instModel.addApeInstantiation(new APEInstantiation(25, "a = b + 17; int c = 2*d+a;"));
        
        instModel.saveToFile(Paths.get(
                "/home/dscheurer/key-workspace/GIT/key/key/key.ui/examples/abstract_execution/instantiation_checking/SlideStatements/slideStatementsInstP1.aei").toFile());

//        final InstantiationChecker checker = new InstantiationChecker(instModel);
//        checker.proveInstantiation(true);
    }
}
