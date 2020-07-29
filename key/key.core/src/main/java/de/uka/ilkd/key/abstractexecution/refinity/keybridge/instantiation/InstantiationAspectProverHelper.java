// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is public by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.keybridge.instantiation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.CompletionCondition;
import de.uka.ilkd.key.abstractexecution.refinity.keybridge.InvalidSyntaxException;
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
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.GenericTermReplacer;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.KeYJMLPreParser;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.util.Triple;
import recoder.ModelException;

/**
 * @author Dominic Steinhoefel
 */
public class InstantiationAspectProverHelper {
    private static final String JAVA_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/Problem.java";
    private static final String APE_RETRIEVAL_PROBLEM_FILE_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/programRetrievalProblem.key";
    private static final String KEY_HEADER_SCAFFOLD = "/de/uka/ilkd/key/refinity/instantiation/header.key";

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

    private final String keyHeaderScaffold;

    /** A cached list of APEs in the model to save time. */
    private Optional<List<APERetrievalResult>> apes = Optional.empty();

    private final Profile profile;

    /**
     * A "dummy" {@link Services} object with no associated proof, but with
     * namespaces populated according to the definitions in the instantiation model.
     * USE WITH CAUTION! When mixing this with other services from newly parsed key
     * files etc., it can easily lead to terms with inconsistent variable names. It
     * should be safe when only converting logic elements to text for writing in a
     * key file, but it shouldn't be used when compiling a {@link Term} object.
     */
    private Services services = null;

    public InstantiationAspectProverHelper() {
        javaScaffold = KeyBridgeUtils.readResource(JAVA_PROBLEM_FILE_SCAFFOLD);
        keyRetrieveAPEsScaffold = KeyBridgeUtils.readResource(APE_RETRIEVAL_PROBLEM_FILE_SCAFFOLD);
        keyHeaderScaffold = KeyBridgeUtils.readResource(KEY_HEADER_SCAFFOLD);
        this.profile = new JavaProfile();
    }

    public InstantiationAspectProverHelper(final Profile profile) {
        javaScaffold = KeyBridgeUtils.readResource(JAVA_PROBLEM_FILE_SCAFFOLD);
        keyRetrieveAPEsScaffold = KeyBridgeUtils.readResource(APE_RETRIEVAL_PROBLEM_FILE_SCAFFOLD);
        keyHeaderScaffold = KeyBridgeUtils.readResource(KEY_HEADER_SCAFFOLD);
        this.profile = profile;
    }

    public String createJavaFile(final AEInstantiationModel model, final String origProgram) {
        final String paramsDecl = model.getProgramVariableDeclarations().stream()
                .map(decl -> String.format("%s %s", decl.getTypeName(), decl.getVarName()))
                .collect(Collectors.joining(","));

        final Function<String, String> addBlocks;
        final Function<String, String> escapeDL;
        final Function<String, String> indent;
        final Function<String, String> instantiate;
        final Function<String, String> combined;

        {
            addBlocks = p -> KeyBridgeUtils.addBlocksAfterConstraints(p);
            escapeDL = p -> KeyBridgeUtils.escapeDL(p, model.getAbstractLocationSets(),
                    model.getPredicateDeclarations(), model.getFunctionDeclarations());
            indent = p -> p.replaceAll("\n", "\n        ");
            instantiate = p -> substituteLocsetValueInstsInString(p, model);

            // NOTE (DS, 2020-06-24): It seems to be crucial to execute addBlocks
            // first, otherwise, I got a StackOverflowError for one example. A closer
            // Look at the thing is eventually required...

            combined = addBlocks //
                    .andThen(instantiate) //
                    .andThen(escapeDL) //
                    .andThen(indent);
        }

        final String program = combined.apply(origProgram);

        final String context = combined.apply(model.getMethodLevelContext());

        return javaScaffold.replaceAll(PARAMS, paramsDecl)
                .replaceAll(BODY, Matcher.quoteReplacement(program))
                .replaceAll(CONTEXT, Matcher.quoteReplacement(context));
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
            proof = KeyBridgeUtils.createProofAndRun(keyFileContent, javaFileContent, maxNumSteps,
                    profile);
        } catch (RuntimeException rte) {
            throw new UnsuccessfulAPERetrievalException(rte.getMessage(), rte.getCause());
        }
        assert !proof.closed();
        return proof;
    }

    /**
     * Returns the pre- and postcondition pairs for all "completion conditions"
     * (e.g., normal or exceptional behavior).
     * 
     * @param ape The APE for which to retrieve the {@link CompletionCondition}s.
     * @return The list of {@link CompletionCondition}s for the given
     * {@link APERetrievalResult}.
     */
    public List<CompletionCondition> getCompletionConditions(final AEInstantiationModel model,
            final APEInstantiation inst) {
        final LocationVariable resultVar = (LocationVariable) services.getNamespaces()
                .programVariables().lookup("result");
        assert resultVar != null;

        final List<CompletionCondition> result = new ArrayList<>();

        final List<TextualJMLSpecCase> specs = getAPE(model, inst).getJMLConstructs().stream()
                .filter(TextualJMLSpecCase.class::isInstance).map(TextualJMLSpecCase.class::cast)
                .filter(c -> c.getBehavior() != Behavior.NONE).collect(Collectors.toList());

        final Function<ImmutableList<PositionedString>, Optional<String>> defaultMapper = list -> list
                .isEmpty() ? Optional.empty()
                        : Optional.of(list.stream().map(str -> str.text)
                                .collect(Collectors.joining(" && ")));

        for (final TextualJMLSpecCase spec : specs) {
            final Behavior behavior = spec.getBehavior();
            final String precondition = defaultMapper.apply(spec.getRequires())
                    .map(pre -> KeyBridgeUtils.jmlStringToJavaDLString(pre,
                            KeyBridgeUtils.dummyKJT(), null, services))
                    .orElse(null);

            final String postcondition = defaultMapper.apply(spec.getEnsures())
                    .map(pre -> KeyBridgeUtils.jmlStringToJavaDLString(pre,
                            KeyBridgeUtils.dummyKJT(), resultVar, services))
                    .orElse(null);

            // TODO: Check behavior w.r.t. special variables (e.g., \result)

            result.add(new CompletionCondition(behavior, precondition, postcondition));
        }

        return result;
    }

    /**
     * Tries to parse the loaded {@link AEInstantiationModel} and returns
     * information about the first found JML/Java error: Message, line, and column
     * number.
     * 
     * @return Information about the first found JML/Java-Error or an empty
     * {@link Optional}.
     */
    public Optional<Triple<String, Integer, Integer>> getFirstKeYJMLParserErrorMessage(
            final AEInstantiationModel model) {
        try {
            createRetrievalProof(model, 0, model.getProgram());
        } catch (UnsuccessfulAPERetrievalException exc) {
            if (exc.getCause() instanceof ModelException) {
                final ModelException mexc = (ModelException) exc.getCause();

                final Pattern p = Pattern.compile("@([0-9]+)/([0-9]+)");
                final Matcher m = p.matcher(mexc.getMessage());

                if (!m.matches()) {
                    return Optional.empty();
                }

                return Optional.of(new Triple<>(mexc.getMessage(), Integer.parseInt(m.group(1)) - 3,
                        Integer.parseInt(m.group(2)) - 8));
            } else if (exc.getCause() instanceof SLTranslationException) {
                final SLTranslationException slte = (SLTranslationException) exc.getCause();
                return Optional.of(new Triple<>(slte.getMessage(), slte.getPosition().getLine() - 3,
                        slte.getPosition().getColumn() - 8));
            }
        }

        return Optional.empty();
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

    public Services getPopulatedDummyServices(final AEInstantiationModel model) {
        if (services != null) {
            return KeyBridgeUtils.copyWithKeyProgModelInfo(services);
        }

        services = KeyBridgeUtils.dummyServices();
        model.getProgramVariableDeclarations().stream()
                .map(pvDecl -> new ProgramVariableDeclaration(pvDecl.getTypeName(),
                        "_" + pvDecl.getVarName()))
                .forEach(pvDecl -> pvDecl.checkAndRegister(services));

        model.fillNamespacesFromModel(services);

        return services;
    }

    /**
     * Instantiates function and predicate symbols in the given formula with their
     * instantiations. E.g., "returnsA(\value(footprintA))" is first instantiated to
     * "returnsA(\value(x), \value(y))" (if footprintA is instantiated to "x, y"),
     * and then the whole predicate is replaced by the instantiating formula, e.g.,
     * "x == null". Returns a String representation of the result.
     * 
     * @param formulaStr The formula which should be instantiated (e.g., a pre- or
     * postcondition).
     * @param model The {@link AEInstantiationModel} for instantiations of function
     * and predicate symbols.
     * @param services The {@link Services} object (primarily for namespaces!)
     * @return The instantiated String
     * @throws RecognitionException if there was a syntax error in the (abstract)
     * formula formulaStr, or in the instantiating functions / predications.
     */
    public String instantiate(final String formulaStr, final AEInstantiationModel model,
            final Services services) throws RecognitionException {
        Term formula = KeyBridgeUtils.parseTerm( //
                substituteLocsetValueInstsInString(formulaStr, model),
                new GoalLocalSpecificationRepository(), services);

        for (final FunctionInstantiation finst : model.getFunctionInstantiations()) {
            final de.uka.ilkd.key.logic.op.Function func = services.getNamespaces().functions()
                    .lookup(finst.getDeclaration().getFuncName());
            assert func != null;

            final Term inst = KeyBridgeUtils.parseTerm(finst.getInstantiation(),
                    new GoalLocalSpecificationRepository(), services);

            formula = GenericTermReplacer.replace( //
                    formula, t -> t.op() == func, t -> inst, services);
        }

        for (final PredicateInstantiation finst : model.getPredicateInstantiations()) {
            final de.uka.ilkd.key.logic.op.Function pred = services.getNamespaces().functions()
                    .lookup(finst.getDeclaration().getPredName());
            assert pred != null;

            final Term inst = KeyBridgeUtils.parseTerm(finst.getInstantiation(),
                    new GoalLocalSpecificationRepository(), services);

            formula = GenericTermReplacer.replace( //
                    formula, t -> t.op() == pred, t -> inst, services);
        }

        return KeyBridgeUtils.termToString(formula, services);
    }

    /**
     * Returns a header for a KeY proof, including declarations of variables in the
     * instantiation.
     * 
     * @param inst The instantiation (for declaring free variables).
     * @return The header.
     */
    public String keyFileHeader(final AEInstantiationModel model, final APEInstantiation inst) {
        final LinkedHashSet<LocationVariable> instProgVars;

        {
            final RetrieveProgramResult retrProgRes = retrieveProgram(model,
                    inst.getInstantiation());
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

        return keyHeaderScaffold
                .replaceAll(FUNCTIONS,
                        Matcher.quoteReplacement(
                                InstantiationAspectProverHelper.createFuncDecls(model)))
                .replaceAll(PREDICATES,
                        Matcher.quoteReplacement(
                                InstantiationAspectProverHelper.createPredDecls(model)))
                .replaceAll(PROGRAMVARIABLES, Matcher.quoteReplacement(
                        InstantiationAspectProverHelper.createProgvarDecls(model) + newVars));
    }

    public Profile profile() {
        return profile;
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
    public List<APERetrievalResult> retrieveAPEs(final AEInstantiationModel model) {
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
     * Returns the abstract program element for the given instantiation.
     * 
     * @param model The {@link AEInstantiationModel}.
     * @param inst The {@link APEInstantiation} determining the
     * {@link AbstractProgramElement} to receive.
     * @return The {@link AbstractProgramElement}.
     * @throws UnsuccessfulAPERetrievalException if no or more than 1 instantiation
     * are found.
     */
    public APERetrievalResult getAPEForInst(final AEInstantiationModel model,
            final APEInstantiation inst) {
        final List<APERetrievalResult> results = retrieveAPEs(model).stream()
                .filter(r -> r.line == inst.getApeLineNumber()).collect(Collectors.toList());

        if (results.size() != 1) {
            throw new UnsuccessfulAPERetrievalException(
                    String.format("Found %d APEs for instantiations, expected 1", results.size()));
        }

        return results.get(0);
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
    public RetrieveProgramResult retrieveProgram(final AEInstantiationModel model,
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
     * Returns the APE for the designated instantiation.
     * 
     * @param model The model in which the APE referred to by the instantiation is
     * contained.
     * @param inst The instantiation.
     * @return The requested APE.
     * @throws UnsuccessfulAPERetrievalException If the requested APE could not be
     * found.
     */
    private APERetrievalResult getAPE(final AEInstantiationModel model, final APEInstantiation inst)
            throws UnsuccessfulAPERetrievalException {
        return retrieveAPEs(model).stream().filter(r -> r.getLine() == inst.getApeLineNumber())
                .findFirst()
                .orElseThrow(() -> new UnsuccessfulAPERetrievalException(
                        "Expected to find APE with line no. " + inst.getApeLineNumber()
                                + ", but did not."));
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
                jmlAssignableTerm, KeyBridgeUtils.dummyKJT(), null,
                services.getNamespaces().programVariables().allElements().stream()
                        .map(ProgramVariable.class::cast)
                        .collect(ImmutableSLList.toImmutableList()),
                services);
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
        final APERetrievalResult ape = getAPE(model, inst);
        final String jmlAssignableTermCSVList = getJMLAssignableOrAccessibleTerm(ape, assignable);

        return Arrays.stream(jmlAssignableTermCSVList.split(",")).map(String::trim)
                .collect(Collectors.toList());
    }

    /**
     * Substitutes the location set instantiations in value terms, e.g.,
     * "<code>\value(footprintA)</code>" ->
     * "<code>\value(singletonPV(PV(x))), \value(...), ...</code>".
     * 
     * @param substIn The string in which to perform the substitution.
     * @param model The {@link AEInstantiationModel} (for the substitutions).
     * @return The instantiated String.
     */
    private String substituteLocsetValueInstsInString(final String substIn,
            final AEInstantiationModel model) {
        /* non-final */ String result = substIn;

        for (final FunctionInstantiation inst : model.getFunctionInstantiations().stream()
                .filter(finst -> finst.getDeclaration().getResultSortName().equals("LocSet"))
                .collect(Collectors.toList())) {
            final String locsetTermStr = inst.getInstantiation();
            final Services services = getPopulatedDummyServices(model);

            final String valPattern = Pattern.quote("\\value") + "\\s*\\(\\s*"
                    + Pattern.quote(inst.getDeclaration().getFuncName()) + "\\s*\\)";

            final String instantiation = Matcher.quoteReplacement( //
                    locsetsFromLocsetString(locsetTermStr, services).stream()
                            .map(t -> String.format("%s\\value(%s)",
                                    typeCastForLocsetSingleton(t, services),
                                    KeyBridgeUtils.termToString(t, services).replaceAll("\n", "")))
                            .collect(Collectors.joining(",")));

            result = result.replaceAll(valPattern, instantiation);
        }

        return result;
    }

    /**
     * Given a singletonPV, singleton, or abstract locset, returns a type cast
     * "(TYPE) ". For an abstract locset, returns the empty string.
     * 
     * @param t The term from which to obtain the type cast.
     * @return The type cast.
     */
    private String typeCastForLocsetSingleton(final Term t, final Services services) {
        final Operator op = t.op();
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();

        if (op == locSetLDT.getSingletonPV()) {
            return "(" + ((LocationVariable) t.sub(0).sub(0).op()).sort().name().toString() + ") ";
        } else if (op == locSetLDT.getSingleton()) {
            System.err.println(
                    "Unimplemented: Get type cast for singleton locations (InstantiationAspectProverHelper)");
        }

        return "";
    }

    public static String createFuncDecls(final AEInstantiationModel model) {
        final String functionsDecl;

        {
            final String locSetDecls = model.getAbstractLocationSets().stream()
                    .map(FunctionDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));

            final String userDefinedFuncDeclsInst = model.getFunctionInstantiations().stream()
                    .filter(inst -> !inst.getDeclaration().getResultSortName().equals("LocSet"))
                    .map(FunctionInstantiation::toDeclarationString)
                    .collect(Collectors.joining("\n  "));

            final String userDefinedFuncDeclsUnInst = model.getFunctionDeclarations().stream()
                    .filter(decl -> !model.getFunctionInstantiations().stream()
                            .map(FunctionInstantiation::getDeclaration)
                            .anyMatch(decl2 -> !decl.getFuncName().equals(decl2.getFuncName())))
                    .map(FunctionDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));

            String userDefinedFuncDecls = userDefinedFuncDeclsInst;
            if (!userDefinedFuncDeclsInst.isEmpty() && !userDefinedFuncDeclsUnInst.isEmpty()) {
                userDefinedFuncDecls += "\n";
            }
            userDefinedFuncDecls += userDefinedFuncDeclsUnInst;

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
     * @return A string representing the instantiations of symbolic functions and
     * predicates.
     */
    public static String createLocSetInstAssumptions(final AEInstantiationModel model) {
        /*
         * NOTE (DS, 2020-06-27): We're currently only creating instantiation
         * assumptions for LocSet constants, and are for now disregarding parametric
         * location sets. This should be considered in the future.
         */

        return model.getFunctionInstantiations().stream()
                .filter(inst -> inst.getDeclaration().getResultSortName().equals("LocSet"))
                .filter(inst -> inst.getInstArgSorts().size() == 0
                        && inst.getDeclaration().getArgSorts().size() == 0)
                .map(inst -> String.format("%s = %s", inst.getDeclaration().getFuncName(),
                        inst.getInstantiation()))
                .collect(Collectors.joining(" &\n  "));
    }

    public static String createParams(final AEInstantiationModel model) {
        final String params = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::getVarName).collect(Collectors.joining(","));
        return params;
    }

    public static String createPredDecls(final AEInstantiationModel model) {
        final String instPredicatesDecl = model.getPredicateInstantiations().stream()
                .map(PredicateInstantiation::toDeclarationString)
                .collect(Collectors.joining("\n  "));

        final String additionalPredicatesDecl = model.getPredicateDeclarations().stream()
                .filter(decl -> !model.getPredicateInstantiations().stream()
                        .map(PredicateInstantiation::getDeclaration)
                        .anyMatch(decl2 -> !decl.getPredName().equals(decl2.getPredName())))
                .map(PredicateDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));

        return instPredicatesDecl
                + (!instPredicatesDecl.isEmpty() && !additionalPredicatesDecl.isEmpty() ? "\n  "
                        : "")
                + additionalPredicatesDecl;
    }

    public static String createProgvarDecls(final AEInstantiationModel model) {
        final String progvarsDecl = model.getProgramVariableDeclarations().stream()
                .map(ProgramVariableDeclaration::toKeYFileDecl).collect(Collectors.joining("\n  "));
        return progvarsDecl;
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

    private static ImmutableSet<Term> locsetsFromLocsetString(final String locsetTermStr,
            final Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Term parsed;
        try {
            parsed = KeyBridgeUtils.parseTerm(locsetTermStr, new GoalLocalSpecificationRepository(),
                    services);
        } catch (RecognitionException e) {
            throw new InvalidSyntaxException("Could not parse LocSet expression", e);
        }

        return tb.locsetUnionToSet(parsed);
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

    public static class APERetrievalResult {
        private final int line;
        private final AbstractProgramElement ape;
        private final List<TextualJMLConstruct> jmlConstructs;
        private final Proof proof;

        public APERetrievalResult(final AbstractProgramElement ape,
                final List<TextualJMLConstruct> jmlConstructs, final Proof proof) {
            this.ape = ape;
            this.jmlConstructs = jmlConstructs;
            // There's a shift of 3 lines in the dummy Java file.
            this.line = ape.getStartPosition().getLine() - 3;
            this.proof = proof;
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

        public Services getServices() {
            return proof.getServices();
        }

        public GoalLocalSpecificationRepository getLocalSpecRepo() {
            return proof.openGoals().head().getLocalSpecificationRepository();
        }
    }

    private static class CollectAPEVisitor extends JavaASTVisitor {
        private final List<APERetrievalResult> result = new ArrayList<>();
        private final Proof proof;

        public CollectAPEVisitor(ProgramElement root,
                GoalLocalSpecificationRepository localSpecRepo, Services services) {
            super(root, localSpecRepo, services);
            this.proof = services.getProof();
        }

        @Override
        public void doDefaultAction(SourceElement node) {
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

                result.add(new APERetrievalResult(ape, jmlConstructs, proof));
            }
        }

        public List<APERetrievalResult> getResult() {
            return result;
        }
    }

}
