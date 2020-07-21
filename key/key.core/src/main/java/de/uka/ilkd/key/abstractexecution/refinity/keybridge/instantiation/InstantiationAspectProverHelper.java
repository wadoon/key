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
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.RetrieveProgramResult;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.UnsuccessfulAPERetrievalException;
import de.uka.ilkd.key.abstractexecution.refinity.model.FunctionDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.PredicateDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.ProgramVariableDeclaration;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.AEInstantiationModel;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.APEInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.FunctionInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.model.instantiation.PredicateInstantiation;
import de.uka.ilkd.key.abstractexecution.refinity.util.KeyBridgeUtils;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.KeYJMLPreParser;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import recoder.ModelException;

/**
 * @author Dominic Steinhoefel
 */
public class InstantiationAspectProverHelper {
    public static final InstantiationAspectProverHelper INSTANCE = new InstantiationAspectProverHelper();

    private static final String JAVA_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/Problem.java";
    private static final String APE_RETRIEVAL_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/programRetrievalProblem.key";

    private static final String BODY = "<BODY>";
    private static final String CONTEXT = "<CONTEXT>";
    private static final String PARAMS = "<PARAMS>";

    private static final String PROGRAMVARIABLES = "<PROGRAMVARIABLES>";
    private static final String PREDICATES = "<PREDICATES>";
    private static final String FUNCTIONS = "<FUNCTIONS>";
    private static final String PRECONDITION = "<PRECONDITION>";
    private static final String INIT_VARS = "<INIT_VARS>";
    private static final String ADDITIONAL_PREMISES = "<ADDITIONAL_PREMISES>";
    private static final String PROOF = "<PROOF>";

    private final String javaScaffold;
    private final String keyRetrieveAPEsScaffold;

    /** A cached list of APEs in the model to save time. */
    private Optional<List<APERetrievalResult>> apes = Optional.empty();

    /**
     * A "dummy" {@link Services} object with no associated proof, but with
     * namespaces populated according to the definitions in the instantiation model.
     * USE WITH CAUTION! When mixing this with other services from newly parsed key
     * files etc., it can easily lead to terms with inconsistent variable names. It
     * should be safe when only converting logic elements to text for writing in a
     * key file, but it shouldn't be used when compiling a {@link Term} object.
     */
    private Services services = null;

    private InstantiationAspectProverHelper() {
        javaScaffold = KeyBridgeUtils.readResource(JAVA_PROBLEM_FILE_SCAFFOLD);
        keyRetrieveAPEsScaffold = KeyBridgeUtils.readResource(APE_RETRIEVAL_PROBLEM_FILE_SCAFFOLD);
    }

    protected Services getPopulatedDummyServices(final AEInstantiationModel model) {
        if (services != null) {
            return services.copy(false);
        }

        services = KeyBridgeUtils.dummyServices();
        model.getProgramVariableDeclarations().stream()
                .map(pvDecl -> new ProgramVariableDeclaration(pvDecl.getTypeName(),
                        "_" + pvDecl.getVarName()))
                .forEach(pvDecl -> pvDecl.checkAndRegister(services));

        model.fillNamespacesFromModel(services);

        return services;
    }

    protected String createJavaFile(final AEInstantiationModel model,
            final String bodyReplacement) {
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
    protected List<APERetrievalResult> retrieveAPEs(final AEInstantiationModel model) {
        if (apes.isPresent()) {
            return apes.get();
        }

        final RetrieveProgramResult retrProgRes = retrieveProgram(model, model.getProgram());

        final CollectAPEVisitor visitor = new CollectAPEVisitor(retrProgRes.getProgram(),
                retrProgRes.getLocalSpecRepo(), retrProgRes.getServices());
        visitor.start();

        final List<APERetrievalResult> result = visitor.getResult();

        // Cache result 
        this.apes = Optional.of(result);

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
    protected RetrieveProgramResult retrieveProgram(final AEInstantiationModel model,
            final String code) {
        final Proof proof = createRetrievalProof(model, 80, code);

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
    public Proof createRetrievalProof(final AEInstantiationModel model, final int maxNumSteps,
            final String program) throws UnsuccessfulAPERetrievalException {
        final String keyFileContent = createRetrievalKeYFile(model);
        final String javaFileContent = createJavaFile(model, program);

        final Proof proof;
        try {
            proof = KeyBridgeUtils.createProofAndRun(keyFileContent, javaFileContent, maxNumSteps);
        } catch (RuntimeException rte) {
            throw new UnsuccessfulAPERetrievalException(rte.getMessage(), rte.getCause());
        }
        assert !proof.closed();
        return proof;
    }

    protected static String createParams(final AEInstantiationModel model) {
        final String params = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::getVarName).collect(Collectors.joining(","));
        return params;
    }

    protected static String createProgvarDecls(final AEInstantiationModel model) {
        final String progvarsDecl = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));
        return progvarsDecl;
    }

    protected static String createPredDecls(final AEInstantiationModel model) {
        final String predicatesDecl = model.getPredicateDeclarations().stream()
                .map(PredicateDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));
        return predicatesDecl;
    }

    protected static String createFuncDecls(final AEInstantiationModel model) {
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

    /**
     * Returns the assignable term of the given {@link APEInstantiation}.
     * 
     * @param model The {@link AEInstantiationModel} containing the APE to analyze.
     * @param inst The instantiation corresponding to the APE to analyze.
     * @param services The {@link Services} object.
     * @return The assignable JML term.
     * @throws UnsuccessfulAPERetrievalException
     */
    public Term getJMLAssignableTerm(final AEInstantiationModel model, final APEInstantiation inst,
            Services services) throws UnsuccessfulAPERetrievalException {
        return getJMLAssignableOrAccessibleTerm(model, inst, true, services);
    }

    /**
     * Returns the accessible term of the given {@link APEInstantiation}.
     * 
     * @param model The {@link AEInstantiationModel} containing the APE to analyze.
     * @param inst The instantiation corresponding to the APE to analyze.
     * @param services The {@link Services} object.
     * @return The accessible JML term.
     * @throws UnsuccessfulAPERetrievalException
     */
    public Term getJMLAccessibleTerm(final AEInstantiationModel model, final APEInstantiation inst,
            Services services) throws UnsuccessfulAPERetrievalException {
        return getJMLAssignableOrAccessibleTerm(model, inst, false, services);
    }

    /**
     * Returns the accessible term string of the given {@link APEInstantiation}.
     * 
     * @param model The {@link AEInstantiationModel} containing the APE to analyze.
     * @param inst The instantiation corresponding to the APE to analyze.
     * @param services The {@link Services} object.
     * @return The accessible JML term.
     * @throws UnsuccessfulAPERetrievalException
     */
    public String getJavaDLAccessibleTermString(final AEInstantiationModel model,
            final APEInstantiation inst, Services services)
            throws UnsuccessfulAPERetrievalException {
        return LogicPrinter.quickPrintTerm(
                getJMLAssignableOrAccessibleTerm(model, inst, false, services), services, false,
                false);
    }

    /**
     * Returns the assignable or accessible term of the given
     * {@link APEInstantiation}.
     * 
     * @param model The {@link AEInstantiationModel} containing the APE to analyze.
     * @param inst The instantiation corresponding to the APE to analyze.
     * @param assignable true if the assignable spec should be returned, false if
     * the accessible spec should be returned.
     * @param services The {@link Services} object.
     * @return The assignable or accessible JML term.
     * @throws UnsuccessfulAPERetrievalException
     */
    private Term getJMLAssignableOrAccessibleTerm(final AEInstantiationModel model,
            final APEInstantiation inst, boolean assignable, Services services)
            throws UnsuccessfulAPERetrievalException {
        final List<String> jmlAssignables = getJMLAssignableOrAccessibleTerms(model, inst,
                assignable);

        // Translate comma-separated list into \set_union term
        final String jmlAssignableTerm = jmlAssignables.stream().collect(Collectors
                .reducing("\\empty", (a1, a2) -> String.format("\\set_union(%s, %s)", a1, a2)));

        return KeyBridgeUtils.jmlStringToJavaDLTerm( //
                jmlAssignableTerm, KeyBridgeUtils.dummyKJT(), services);
    }

    /**
     * Returns the JML assignable terms from the APE corresponding to the given
     * instantiation.
     * 
     * @param model The {@link AEInstantiationModel} containing the APE to analyze.
     * @param inst The instantiation corresponding to the APE to analyze.
     * @return The assignables for the APE.
     * @throws UnsuccessfulAPERetrievalException If the APE corresponding to the
     * instantiation could not be found.
     */
    public List<String> getJMLAssignableTerms(final AEInstantiationModel model,
            final APEInstantiation inst) throws UnsuccessfulAPERetrievalException {
        return getJMLAssignableOrAccessibleTerms(model, inst, true);
    }

    /**
     * Returns the JML assignable or accessible terms from the APE corresponding to
     * the given instantiation.
     * 
     * @param model The {@link AEInstantiationModel} containing the APE to analyze.
     * @param inst The instantiation corresponding to the APE to analyze.
     * @param assignable true if the assignable spec should be returned, false if
     * the accessible spec should be returned.
     * @return The assignables for the APE.
     * @throws UnsuccessfulAPERetrievalException If the APE corresponding to the
     * instantiation could not be found.
     */
    private List<String> getJMLAssignableOrAccessibleTerms(final AEInstantiationModel model,
            final APEInstantiation inst, boolean assignable)
            throws UnsuccessfulAPERetrievalException {
        final String jmlAssignableTermCSVList = getJMLAssignableOrAccessibleTerm(retrieveAPEs(model)
                .stream().filter(r -> r.getLine() == inst.getApeLineNumber()).findFirst()
                .orElseThrow(() -> new UnsuccessfulAPERetrievalException(
                        "Expected to find APE with line no. " + inst.getApeLineNumber()
                                + ", but did not.")),
                assignable);

        return Arrays.stream(jmlAssignableTermCSVList.split(",")).map(String::trim)
                .collect(Collectors.toList());
    }

    /**
     * Returns the assignable or accessible String of the given APE.
     * 
     * @param ape The {@link APERetrievalResult}.
     * @param assignable true if the assignable spec should be returned, false if
     * the accessible spec should be returned.
     * @return The assignable or accessible specification.
     */
    private static String getJMLAssignableOrAccessibleTerm(final APERetrievalResult ape,
            boolean assignable) {
        final Predicate<TextualJMLSpecCase> filter = assignable ? //
                (c -> c.getAssignable() != null) : (c -> c.getAccessible() != null);

        final Function<TextualJMLSpecCase, ImmutableList<PositionedString>> getter = assignable
                ? TextualJMLSpecCase::getAssignable
                : TextualJMLSpecCase::getAccessible;

        final String keyword = assignable ? "assignable" : "accessible";

        return ape.getJMLConstructs().stream().filter(TextualJMLSpecCase.class::isInstance)
                .map(TextualJMLSpecCase.class::cast).filter(c -> c.getBehavior() == Behavior.NONE)
                .filter(filter).map(getter).map(ImmutableList::head).findAny().map(str -> str.text)
                .map(str -> str.replaceAll(keyword + " ", "")).map(str -> str.replaceAll(";", ""))
                .orElse("\\everything");
    }

    private String createRetrievalKeYFile(final AEInstantiationModel model) {
        final String initVars = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::getVarName)
                .map(pv -> String.format("%s:=_%s", pv, pv)).collect(Collectors.joining("||"));

        final Services services = getPopulatedDummyServices(model);

        final String javaDLPreCondRelation = KeyBridgeUtils.createJavaDLPreCondition(
                model.getPreCondition(), model.getProgramVariableDeclarations(),
                model.getAbstractLocationSets(), model.getPredicateDeclarations(),
                model.getFunctionDeclarations(), KeyBridgeUtils.dummyKJT(), services);

        return keyRetrieveAPEsScaffold
                .replaceAll(FUNCTIONS, Matcher.quoteReplacement(createFuncDecls(model)))
                .replaceAll(PREDICATES, Matcher.quoteReplacement(createPredDecls(model)))
                .replaceAll(PROGRAMVARIABLES, Matcher.quoteReplacement(createProgvarDecls(model)))
                .replaceAll(INIT_VARS,
                        initVars.isEmpty() ? "" : (Matcher.quoteReplacement("{" + initVars + "}")))
                .replaceAll(PARAMS, Matcher.quoteReplacement(createParams(model)))
                .replaceAll(Pattern.quote(PRECONDITION),
                        Matcher.quoteReplacement(javaDLPreCondRelation))
                .replaceAll(ADDITIONAL_PREMISES,
                        Matcher.quoteReplacement(KeyBridgeUtils
                                .createAdditionalPremises(model.getAbstractLocationSets())))
                .replaceAll(PROOF, "" /* unused... */);
    }

    /**
     * @return A string representing the instantiations of symbolic functions and
     * predicates.
     */
    protected static String createSymInsts(final AEInstantiationModel model) {
        final String funcInsts = model.getFunctionInstantiations().stream()
                .map(FunctionInstantiation::toString).collect(Collectors.joining(" &\n  "));
        final String predInsts = model.getPredicateInstantiations().stream()
                .map(PredicateInstantiation::toString).collect(Collectors.joining(" &\n  "));
        return funcInsts.isEmpty() ? (predInsts.isEmpty() ? "true" : predInsts)
                : (predInsts.isEmpty() ? funcInsts : funcInsts + " &\n  " + predInsts);
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

}
