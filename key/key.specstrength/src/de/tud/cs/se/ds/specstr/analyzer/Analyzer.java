// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.tud.cs.se.ds.specstr.analyzer;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.tud.cs.se.ds.specstr.profile.StrengthAnalysisSEProfile;
import de.tud.cs.se.ds.specstr.rule.AbstractAnalysisRule;
import de.tud.cs.se.ds.specstr.rule.AnalyzeInvImpliesLoopEffectsRule;
import de.tud.cs.se.ds.specstr.rule.AnalyzePostCondImpliesMethodEffectsRule;
import de.tud.cs.se.ds.specstr.rule.FactAnalysisRule;
import de.tud.cs.se.ds.specstr.util.GeneralUtilities;
import de.tud.cs.se.ds.specstr.util.JavaTypeInterface;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofVisitor;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Loads the supplied method and performs the strength analysis. Access
 * {@link #analyze()} for starting the analysis. The returned
 * {@link AnalyzerResult} can be printed out using
 * {@link #printResults(AnalyzerResult, PrintStream)}.
 *
 * @author Dominic Steinhoefel
 */
public class Analyzer {
    /**
     * The {@link Logger} for this class.
     */
    private static final Logger LOGGER = LogManager.getFormatterLogger();

    /**
     * The {@link File} including the method to analyze.
     */
    private File file;

    /**
     * The class name for the method to parse.
     */
    private String className;

    /**
     * The method name for the method to parse.
     */
    private String methodName;

    /**
     * The type descriptor for the method to parse.
     */
    private String methodTypeStr;

    /**
     * The {@link SymbExInterface} used in the background.
     */
    private SymbExInterface seIf;

    /**
     * The {@link Optional} {@link File} to save the output in.
     */
    private Optional<File> outProofFile;

    /**
     * An {@link Optional} {@link AnalyzerResult} with the result of the most
     * resent {@link Analyzer} run; only is non-empty after {@link #analyze()} /
     * {@link #analyze(Optional)} has been called.
     */
    private Optional<AnalyzerResult> analyzerResult = Optional.empty();

    /**
     * An {@link Optional} with a {@link Proof} of the most resent
     * {@link Analyzer} run; only is non-empty after {@link #analyze()} /
     * {@link #analyze(Optional)} has been called.
     */
    private Optional<Proof> analyzerProofResult = Optional.empty();

    /**
     * Constructor.
     *
     * @param file
     *            The file containing the method.
     * @param method
     *            The method identifier; should respect the format<br>
     *            <br>
     *
     *            <code>&lt;fully qualified type name&gt;::&lt;method
     *            name&gt;(&lt;arg decl&gt;)&lt;return type decl&gt;</code>,<br>
     *            <br>
     *
     *            where where <code>&lt;arg decl&gt;</code> is according to the
     *            field descriptors in the JVM specification, for instance
     *            <code>[ILjava.lang.Object;D</code> for an integer array, an
     *            Object and a double (not that we would support
     *            doubles...).<br>
     *            <code>&lt;return type decl&gt;</code> is constructed
     *            similarly, only for a single type.
     * @param outProofFile
     *            An {@link Optional} {@link File} for writing the analyzer
     *            results to, when running the {@link Analyzer} from the command
     *            line and not programmatically.
     * @throws RuntimeException
     *             If the method could not be loaded.
     */
    public Analyzer(File file, String method, Optional<File> outProofFile) {
        this(file, method, outProofFile, null);
    }

    /**
     * Constructor.
     *
     * @param file
     *            The file containing the method.
     * @param method
     *            The method identifier; should respect the format<br>
     *            <br>
     *
     *            <code>&lt;fully qualified type name&gt;::&lt;method
     *            name&gt;(&lt;arg decl&gt;)&lt;return type decl&gt;</code>,<br>
     *            <br>
     *
     *            where where <code>&lt;arg decl&gt;</code> is according to the
     *            field descriptors in the JVM specification, for instance
     *            <code>[ILjava.lang.Object;D</code> for an integer array, an
     *            Object and a double (not that we would support
     *            doubles...).<br>
     *            <code>&lt;return type decl&gt;</code> is constructed
     *            similarly, only for a single type.
     * @param outProofFile
     *            An {@link Optional} {@link File} for writing the analyzer
     *            results to, when running the {@link Analyzer} from the command
     *            line and not programmatically.
     * @param env
     *            The {@link KeYEnvironment} for the problem to analyse (based
     *            on the {@link StrengthAnalysisSEProfile}).
     * @throws RuntimeException
     *             If the method could not be loaded.
     */
    public Analyzer(File file, String method, Optional<File> outProofFile,
            KeYEnvironment<DefaultUserInterfaceControl> env) {
        this.file = file;
        if (!parseMethodString(method)) {
            final String errorMsg = GeneralUtilities
                    .format("Error in parsing method descriptor %s", method);
            LOGGER.error(errorMsg);
            throw new RuntimeException(errorMsg);
        }

        try {
            if (env == null) {
                this.seIf = new SymbExInterface(file);
            }
            else {
                this.seIf = new SymbExInterface(file, env);
            }
        }
        catch (ProblemLoaderException e) {
            GeneralUtilities.logErrorAndThrowRTE(LOGGER,
                    "ProblemLoaderException occurred while loading file %s\nMessage:\n%s",
                    file.getName(), e.getMessage());
        }
        this.outProofFile = outProofFile;
    }

    /**
     * An {@link Optional} {@link AnalyzerResult} with the result of the most
     * resent {@link Analyzer} run; only is non-empty after {@link #analyze()} /
     * {@link #analyze(Optional)} has been called.
     *
     * @return The most recent {@link AnalyzerResult} or an empty
     *         {@link Optional}.
     */
    public Optional<AnalyzerResult> result() {
        return analyzerResult;
    }

    /**
     * An {@link Optional} with a {@link Proof} of the most resent
     * {@link Analyzer} run; only is non-empty after {@link #analyze()} /
     * {@link #analyze(Optional)} has been called.
     *
     * @return The most recent {@link Proof} or an empty {@link Optional}.
     */
    public Optional<Proof> proof() {
        return analyzerProofResult;
    }

    /**
     * Performs the actual analysis, and sets the internal
     * {@link AnalyzerResult}, which is also returned to the result. This result
     * can afterward be obtained by calling {@link #result()}.
     *
     * @return An {@link AnalyzerResult} object.
     * @throws RuntimeException
     *             If the results file could not be saved due to an
     *             {@link IOException}.
     */
    public AnalyzerResult analyze() {
        return analyze(Optional.empty());
    }

    /**
     * Performs the actual analysis, and sets the internal
     * {@link AnalyzerResult}, which is also returned to the result. This result
     * can afterward be obtained by calling {@link #result()}.
     *
     * @return An {@link AnalyzerResult} object.
     * @throws RuntimeException
     *             If the results file could not be saved due to an
     *             {@link IOException}.
     */
    public AnalyzerResult analyze(File proofFile) {
        assert proofFile != null;
        try {
            seIf = new SymbExInterface(file, KeYEnvironment.load(proofFile));
            return analyze(Optional.of(seIf.keyEnvironment().getLoadedProof()));
        }
        catch (ProblemLoaderException e) {
            GeneralUtilities.logErrorAndThrowRTE(LOGGER,
                    "%s while loading proof file %s:\n%s",
                    e.getClass().getSimpleName(), proofFile.getName(),
                    e.getMessage());
        }

        return analyze(Optional.empty());
    }

    /**
     * Performs the actual analysis, and sets the internal
     * {@link AnalyzerResult}, which is also returned to the result. This result
     * can afterward be obtained by calling {@link #result()}.
     *
     * @param existingProof
     *            An existing {@link Optional} {@link Proof} object to
     *            re-analyze, in particular after interaction.
     * @return An {@link AnalyzerResult} object.
     * @throws RuntimeException
     *             If the results file could not be saved due to an
     *             {@link IOException}.
     */
    public AnalyzerResult analyze(Optional<Proof> existingProof) {
        LOGGER.info("Analyzing Java file %s", file);

        final ProgramMethod method = findMethod();

        LOGGER.info("Analyzing method %s::%s%s", className, methodName,
                methodTypeStr);

        // TODO: Finishing SE with the macro has the side effect that some goals
        // that would be trivially closable, like exception branches, are closed
        // late since the macro is focusing on SE.

        LOGGER.trace("Building proof tree");
        // Finish symbolic execution
        seIf.finishSEForMethod(method);
        final Proof proof = existingProof.orElse(seIf.proof());

        FactExtractionResult fer;
        if (existingProof.isPresent()) {
            LOGGER.trace("Collecting facts");
            fer = extractFactsFromProofTree(proof);
        }
        else {
            LOGGER.trace("Applying analysis rules and collecting facts");
            fer = applyAnalysisRules(proof);
        }

        final List<Fact> facts = fer.getFacts();
        final int unclosedLoopInvPreservedGoals =
                fer.getUnclosedLoopInvPreservedGoals();
        final int unclosedPostCondSatisfiedGoals =
                fer.getUnclosedPostCondSatisfiedGoals();

        LOGGER.info("Collected %s facts", facts.size());

        LOGGER.info("Proving facts, this may take some time...");

        List<Fact> coveredFacts = new ArrayList<>();
        List<Fact> abstractlyCoveredFacts = new ArrayList<>();
        List<Fact> unCoveredFacts = new ArrayList<>();

        analyzeFacts(facts, coveredFacts, abstractlyCoveredFacts,
                unCoveredFacts);

        LOGGER.trace("Done proving facts.");

        LOGGER.trace("Checking exception branches.");

        final List<ExceptionResult> problematicExceptions = //
                checkExceptionBranches(proof);

        // TODO also check if loop invariants are initially valid.

        LOGGER.trace("Done checking exception branches.");

        if (outProofFile.isPresent()) {
            try {
                LOGGER.info("Writing proof to file %s", outProofFile.get());
                proof.saveToFile(outProofFile.get());
            }
            catch (IOException e) {
                LOGGER.error("Problem writing proof to file %s, message:\n%s",
                        outProofFile.get(), e.getMessage());
            }
        }

        LOGGER.trace("Finished analysis of Java file %s", file);

        final AnalyzerResult result = new AnalyzerResult(coveredFacts,
                abstractlyCoveredFacts,
                unCoveredFacts, problematicExceptions,
                unclosedLoopInvPreservedGoals, unclosedPostCondSatisfiedGoals);

        this.analyzerResult = Optional.of(result);
        this.analyzerProofResult = Optional.of(proof);

        return result;
    }

    /**
     * Extracts facts from a {@link Proof} tree after exhaustive symbolic
     * execution.
     *
     * @param proof
     *            The {@link Proof} tree to extract facts from.
     * @return A {@link FactExtractionResult}.
     */
    private FactExtractionResult extractFactsFromProofTree(Proof proof) {
        final RuleProofVisitor analysisRuleVisitor =
                new RuleProofVisitor(AbstractAnalysisRule.class);
        proof.breadthFirstSearch(proof.root(), analysisRuleVisitor);

        final List<Fact> facts = new ArrayList<>();
        int unclosedLoopInvPreservedGoals = 0;
        int unclosedPostCondSatisfiedGoals = 0;

        for (final Node analysisRuleNode : analysisRuleVisitor.result()) {
            final String readablePathCond =
                    extractReadablePathCondition(
                            analysisRuleNode.parent());

            final Rule analysisRule =
                    analysisRuleNode.getAppliedRuleApp().rule();

            assert analysisRule instanceof AbstractAnalysisRule;

            final FactType factType;
            if (analysisRule instanceof AnalyzeInvImpliesLoopEffectsRule) {
                factType = FactType.LOOP_BODY_FACT;
            }
            else if (analysisRule instanceof AnalyzePostCondImpliesMethodEffectsRule) {
                factType = FactType.POST_COND_FACT;
            }
            else {
                factType = null;
                GeneralUtilities.logErrorAndThrowRTE(LOGGER,
                        "Unknown %s: %s",
                        AbstractAnalysisRule.class.getName(),
                        analysisRule.getClass().getName());
            }

            final Iterable<Node> factNodes = GeneralUtilities
                    .toStream((() -> analysisRuleNode.childrenIterator()))
                    .collect(Collectors.toList());

            for (final Node factNode : factNodes) {
                final String branchLabel =
                        factNode.getNodeInfo().getBranchLabel();

                if (factNode.getAppliedRuleApp() == null
                        || !factNode.getAppliedRuleApp().rule()
                                .equals(FactAnalysisRule.INSTANCE)) {
                    // This is a "post condition satisfied" / "loop invariant
                    // preserved" node and no FactAnalysisRule node -- has to be
                    // treated specially.

                    seIf.applyMacro(new TryCloseMacro(10000), factNode);

                    if (!factNode.isClosed()) {
                        if (branchLabel.equals(
                                AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL)) {
                            unclosedLoopInvPreservedGoals++;
                        }
                        else if (branchLabel.equals(
                                AbstractAnalysisRule.POSTCONDITION_SATISFIED_BRANCH_LABEL)) {
                            unclosedPostCondSatisfiedGoals++;
                        }
                        else {
                            GeneralUtilities.logErrorAndThrowRTE(LOGGER,
                                    "Unknown / unexpected branch label \"%s\" where %s or %s was expected.",
                                    branchLabel,
                                    AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL,
                                    AbstractAnalysisRule.POSTCONDITION_SATISFIED_BRANCH_LABEL);
                        }
                    }

                    continue;
                }

                final String factTitle = branchLabel.split("\"")[1];

                final Iterable<Node> factAnalysisCaseNodes =
                        GeneralUtilities
                                .toStream((() -> factNode
                                        .childrenIterator()))
                                .collect(Collectors.toList());

                if (factType != FactType.POST_COND_FACT &&
                        factCanBeDiscarded(factAnalysisCaseNodes)) {
                    // Discard the fact -- too easy ;)
                    continue;
                }

                facts.add(new Fact(factTitle,
                        readablePathCond, factType,
                        FactAnalysisRule
                                .getFactCoveredNode(factAnalysisCaseNodes),
                        FactAnalysisRule
                                .getFactAbstractlyCoveredNode(
                                        factAnalysisCaseNodes),
                        FactAnalysisRule
                                .getFactAbstractlyCoveredVerifNode(
                                        factAnalysisCaseNodes)));
            }
        }

        return new FactExtractionResult(facts, unclosedLoopInvPreservedGoals,
                unclosedPostCondSatisfiedGoals);
    }

    /**
     * Applies analysis rules and extracts facts from a {@link Proof} tree after
     * exhaustive symbolic execution.
     *
     * @param proof
     *            The {@link Proof} tree to extract facts from.
     * @return A {@link FactExtractionResult}.
     */
    private FactExtractionResult applyAnalysisRules(Proof proof) {
        final List<Node> postConditionNodes = new ArrayList<>();
        final List<Fact> facts = new ArrayList<>();

        int unclosedLoopInvPreservedGoals = 0;
        int unclosedPostCondGoals = 0;

        if (proofHasLoopInvApp(proof)) {
            // Post condition facts. Those have to be extracted *before* the use
            // case facts, since the goals might change that are analyzed for
            // the use case
            unclosedPostCondGoals = extractPostCondFacts(proof, facts);

            // Find "preserves" and "use case" branches
            final List<Node> preservedNodes = new ArrayList<>();

            extractPreservedAndUseCaseNodes(proof, preservedNodes,
                    postConditionNodes);

            // Loop facts
            unclosedLoopInvPreservedGoals = //
                    extractLoopBodyFactsAndShowValidity(//
                            proof, preservedNodes, facts);
        }
        else {
            // Post condition facts
            extractPostCondFacts(proof, facts);
        }

        return new FactExtractionResult(facts, unclosedLoopInvPreservedGoals,
                unclosedPostCondGoals);
    }

    /**
     * Analyzes the {@link List} facts of extracted {@link Fact}s by trying to
     * close the related {@link Goal}s.
     *
     * @param facts
     *            The {@link List} of {@link Fact}s to analyze.
     * @param coveredFacts
     *            The {@link List} into which the covered {@link Fact}s should
     *            be written.
     * @param abstractlyCoveredFacts
     *            The {@link List} into which the abstractly covered
     *            {@link Fact}s should be written.
     * @param unCoveredFacts
     *            The {@link List} into which the uncovered {@link Fact}s should
     *            be written.
     */
    private void analyzeFacts(final List<Fact> facts, List<Fact> coveredFacts,
            List<Fact> abstractlyCoveredFacts, List<Fact> unCoveredFacts) {
        for (Fact fact : facts) {
            LOGGER.trace("Proving fact %s", fact.descr);

            final Node factNode = fact.factCoveredNode;
            seIf.applyMacro(new TryCloseMacro(10000), factNode);

            if (factNode.isClosed()) {
                LOGGER.trace("Fact covered");
                coveredFacts.add(fact);
                fact.setCovered(true);
            }
            else {
                final Node abstractlyCoveredNode =
                        fact.factAbstractlyCoveredNode;
                final Node abstractlyCoveredTestNode =
                        fact.factAbstractlyCoveredTestNode;

                boolean abstractlyCovered = false;
                if (abstractlyCoveredNode != null) {
                    seIf.applyMacro(new TryCloseMacro(10000),
                            abstractlyCoveredNode);
                    seIf.applyMacro(new TryCloseMacro(10000),
                            abstractlyCoveredTestNode);
                    abstractlyCovered = abstractlyCoveredNode.isClosed()
                            && !abstractlyCoveredTestNode.isClosed();
                }

                if (abstractlyCovered) {
                    LOGGER.trace("Fact abstractly covered");
                    abstractlyCoveredFacts.add(fact);
                    fact.setAbstractlyCovered(true);
                }
                else {
                    LOGGER.trace("Fact uncovered");
                    unCoveredFacts.add(fact);
                }
            }
        }
    }

    /**
     * Checks whether the given {@link Proof} has a
     * {@link LoopInvariantBuiltInRuleApp} application.
     *
     * @param proof
     *            The {@link Proof} to check.
     * @return true iff the {@link Proof} has a
     *         {@link LoopInvariantBuiltInRuleApp}.
     */
    private boolean proofHasLoopInvApp(final Proof proof) {
        final RuleAppVisitor ruleAppVisitor = new RuleAppVisitor(
                LoopInvariantBuiltInRuleApp.class);
        proof.breadthFirstSearch(proof.root(), ruleAppVisitor);

        return ruleAppVisitor.success();
    }

    /**
     * Tries to close exception branches, and returns {@link ExceptionResult}s
     * for those for which it was not possible.
     *
     * @param proof
     *            The {@link Proof} object to find the exception branches in.
     * @return A {@link List} of {@link ExceptionResult}s for exception branches
     *         that could not be closed.
     */
    private List<ExceptionResult> checkExceptionBranches(final Proof proof) {
        final List<ExceptionResult> unclosedExceptions = new ArrayList<>();

        // TODO That's a hackish way of filtering exception branches; can we do
        // this more systematically? In any case, the list is incomplete.
        final String[] exceptionBranchLabels = new String[] { //
                "Null Reference", //
                "Index Out of Bounds", //
        };

        final List<Node> exceptionNodes = GeneralUtilities
                .toStream(proof.openGoals()).map(g -> g.node())
                .filter(n -> n.getNodeInfo().getBranchLabel() != null
                        && Arrays.stream(exceptionBranchLabels).anyMatch(
                                s -> n.getNodeInfo().getBranchLabel()
                                        .contains(s)))
                .collect(Collectors.toList());

        for (final Node excNode : exceptionNodes) {
            LOGGER.trace("Checking exception node \"%s\"",
                    excNode.getNodeInfo().getBranchLabel());
            seIf.applyMacro(new TryCloseMacro(), excNode);
            if (!excNode.isClosed()) {
                unclosedExceptions.add(
                        new ExceptionResult(
                                excNode.getNodeInfo().getBranchLabel(),
                                extractReadablePathCondition(excNode)));
            }
        }

        return unclosedExceptions;
    }

    /**
     * Extracts post condition {@link Fact}s, that is equations about the final
     * state after the method execution (or the use case in the presence of a
     * loop).
     *
     * @param proof
     *            The {@link Proof} object.
     * @param facts
     *            A {@link List} of {@link Fact}s; the method will write
     *            {@link Fact}s into this list.
     * @return The number of unclosed "post condition satisfied" goals.
     */
    private int extractPostCondFacts(Proof proof, List<Fact> facts) {
        int numPostCondGoalsNotClosed = 0;

        for (Goal g : proof.openGoals()) {
            final Node postCondNode = g.node();
            final Optional<PosInOccurrence> maybePio = //
                    getPioOfFormulaWhichHadSELabel(postCondNode);

            if (!maybePio.isPresent()) {
                continue;
            }

            if (!AnalyzePostCondImpliesMethodEffectsRule.INSTANCE.isApplicable(//
                    g, maybePio.get())) {
                continue;
            }

            final Iterable<Node> analysisNodes = //
                    GeneralUtilities
                            .toStream(g.apply(
                                    AnalyzePostCondImpliesMethodEffectsRule.INSTANCE
                                            .createApp(maybePio.get(),
                                                    proof.getServices())))
                            .map(goal -> goal.node())
                            .collect(Collectors.toList());

            for (Node analysisNode : analysisNodes) {
                if (!analysisNode.getNodeInfo().getBranchLabel().equals(
                        AbstractAnalysisRule.POSTCONDITION_SATISFIED_BRANCH_LABEL)) {

                    final String readablePathCond =
                            extractReadablePathCondition(
                                    analysisNode.parent());
                    final String branchLabel = analysisNode.getNodeInfo()
                            .getBranchLabel();

                    final Iterable<Node> factAnalysisNodes = //
                            GeneralUtilities
                                    .toStream(proof.getGoal(analysisNode)
                                            .apply(FactAnalysisRule.INSTANCE
                                                    .createApp(null,
                                                            proof.getServices())))
                                    .map(_g -> _g.node())
                                    .collect(Collectors.toList());

                    facts.add(new Fact(branchLabel.split("\"")[1],
                            readablePathCond, FactType.POST_COND_FACT,
                            FactAnalysisRule
                                    .getFactCoveredNode(factAnalysisNodes),
                            FactAnalysisRule.getFactAbstractlyCoveredNode(
                                    factAnalysisNodes),
                            FactAnalysisRule.getFactAbstractlyCoveredVerifNode(
                                    factAnalysisNodes)));
                }
                else {
                    // That's a post condition branch -- try to close it
                    seIf.applyMacro(new TryCloseMacro(10000),
                            analysisNode);
                    if (!analysisNode.isClosed()) {
                        numPostCondGoalsNotClosed++;
                    }
                }
            }
        }

        if (numPostCondGoalsNotClosed > 0) {
            LOGGER.warn(
                    "Specification (method precondition / loop invariant) could "
                            + "be too weak, or post condition / program wrong: "
                            + "%s open preserves goals",
                    numPostCondGoalsNotClosed);
        }

        return numPostCondGoalsNotClosed;
    }

    /**
     * Extracts loop body {@link Fact}s, that is equations about the final state
     * after execution of a loop body.
     *
     * @param proof
     *            The {@link Proof} object.
     * @param preservedNodes
     *            The {@link Node}s containing the "preserved" nodes after the
     *            application of the {@link LoopScopeInvariantRule}.
     * @param facts
     *            A {@link List} of {@link Fact}s; the method will write
     *            {@link Fact}s into this list.
     * @return The number of loop invariant goals that are not preserved.
     */
    private int extractLoopBodyFactsAndShowValidity(final Proof proof,
            final List<Node> preservedNodes, final List<Fact> facts) {
        final Services services = proof.getServices();

        int invariantGoalsNotPreserved = 0;

        for (Node preservedNode : preservedNodes) {
            final Optional<PosInOccurrence> proofOblPio =
                    getPioOfFormulaWhichHadSELabel(
                            preservedNode);

            assert proofOblPio
                    .isPresent() : "There should be a formula with SE label";

            final RuleApp app = AnalyzeInvImpliesLoopEffectsRule.INSTANCE
                    .createApp(proofOblPio.get(), services)
                    .forceInstantiate(proof.getGoal(preservedNode));

            final ImmutableList<Goal> analysisNodesImmList = proof
                    .getSubtreeGoals(preservedNode).head().apply(app);

            final List<Node> analysisNodes = GeneralUtilities
                    .toStream(analysisNodesImmList).map(goal -> goal.node())
                    .filter(n -> !n.getNodeInfo().getBranchLabel().equals(
                            AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL))
                    .collect(Collectors.toList());

            for (Node analysisNode : analysisNodes) {
                final String branchLabel = analysisNode.getNodeInfo()
                        .getBranchLabel();
                final String readablePathCondition =
                        extractReadablePathCondition(
                                analysisNode.parent());

                final Iterable<Node> factAnalysisNodes = //
                        GeneralUtilities.toStream(proof.getGoal(analysisNode)
                                .apply(FactAnalysisRule.INSTANCE.createApp(null,
                                        proof.getServices())))
                                .map(g -> g.node())
                                .collect(Collectors.toList());

                if (factCanBeDiscarded(factAnalysisNodes)) {
                    // Discard the fact -- too easy ;)
                    continue;
                }

                facts.add(new Fact(branchLabel.split("\"")[1],
                        readablePathCondition, FactType.LOOP_BODY_FACT,
                        FactAnalysisRule.getFactCoveredNode(factAnalysisNodes),
                        FactAnalysisRule
                                .getFactAbstractlyCoveredNode(
                                        factAnalysisNodes),
                        FactAnalysisRule
                                .getFactAbstractlyCoveredVerifNode(
                                        factAnalysisNodes)));
            }

            final Optional<Node> maybeActualPreservedNode = GeneralUtilities
                    .toStream(analysisNodesImmList).map(goal -> goal.node())
                    .filter(n -> n.getNodeInfo().getBranchLabel() != null
                            && n.getNodeInfo().getBranchLabel().equals(
                                    AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL))
                    .findAny();
            assert maybeActualPreservedNode.isPresent();

            final Node actualPreservedNode = maybeActualPreservedNode.get();
            seIf.applyMacro(new TryCloseMacro(10000), actualPreservedNode);
            if (!actualPreservedNode.isClosed()) {
                invariantGoalsNotPreserved++;
            }
        }

        if (invariantGoalsNotPreserved > 0) {
            LOGGER.warn(
                    "Loop invariant could be invalid: %s open preserves goals",
                    invariantGoalsNotPreserved);
        }

        return invariantGoalsNotPreserved;
    }

    /**
     * Checks for a list of {@link Node}s of a {@link Fact} whether the fact can
     * be discarded, which is the case if the loop invariant is not needed for
     * showing it.
     *
     * @param analysisNodes
     *            The collection of {@link Node}s for the {@link Fact} to check.
     * @return true iff the fact can be shown without the loop invariant.
     */
    private boolean factCanBeDiscarded(Iterable<Node> analysisNodes) {
        // Discard the fact if it can be proven without the
        // specification
        final Node coveredByTrueNode = FactAnalysisRule
                .getCoveredByTrueNode(analysisNodes);
        seIf.applyMacro(new TryCloseMacro(1000), coveredByTrueNode);

        return coveredByTrueNode.isClosed();
    }

    /**
     * Creates a "readable" path condition for the given {@link Node}. If the
     * path condition could not be computed by the
     * {@link SymbolicExecutionUtil}, a trivial path condition prefixed with
     * "ERROR-PC" is returned.
     *
     * @param analysisNode
     *            The {@link Node} to compute a path condition for.
     * @return The path condition for the {@link Node}.
     */
    private static String extractReadablePathCondition(Node analysisNode) {
        boolean problem = false;
        Term pathCondTerm = analysisNode.proof().getServices()
                .getTermBuilder().tt();

        try {
            pathCondTerm = SymbolicExecutionUtil
                    .computePathCondition(analysisNode, true, true, false);
        }
        catch (ProofInputException e) {
            problem = true;
        }

        return (problem ? "ERROR-PC " : "") + GeneralUtilities
                .cleanWhitespace(LogicPrinter.quickPrintTerm(pathCondTerm,
                        analysisNode.proof().getServices()));
    }

    /**
     * Extracts {@link Proof} {@link Node}s that are representing preserved and
     * use case parts after a {@link LoopScopeInvariantRule} application. Writes
     * the result in the given {@link List}s for preserved and post condition
     * {@link Node}s.
     *
     * @param proof
     *            The {@link Proof} to extract the nodes from.
     * @param preservedNodes
     *            The {@link List} into which to store the preserved nodes.
     * @param postconditionNodes
     *            The {@link List} into which to store the use case / post
     *            condition nodes.
     */
    private void extractPreservedAndUseCaseNodes(final Proof proof,
            final List<Node> preservedNodes,
            final List<Node> postconditionNodes) {
        final Services services = proof.getServices();

        for (Goal g : proof.openGoals()) {
            if (g.node().parent().getAppliedRuleApp()
                    .rule() == AnalyzePostCondImpliesMethodEffectsRule.INSTANCE
                    && g != proof.getSubtreeGoals(g.node().parent()).head()) {
                // We ignore the goals for the strength analysis of post
                // conditions; only the first one after such a rule app will be
                // considered.
                continue;
            }

            final List<LocationVariable> loopScopeIndices = SymbExInterface
                    .findLoopScopeIndeces(g.node());

            if (loopScopeIndices.isEmpty()) {
                continue;
            }

            final boolean isFalseLsiPresent = loopScopeIndices.stream()
                    .anyMatch(lsi -> {
                        Optional<Term> maybeRHS = GeneralUtilities
                                .toStream(g.node().sequent().succedent())
                                .map(sf -> sf.formula())
                                .filter(
                                        f -> f.op() instanceof UpdateApplication)
                                .map(f -> {
                                    ImmutableArray<Term> values =
                                            SymbolicExecutionUtil
                                                    .extractValueFromUpdate(
                                                            f.sub(0),
                                                            lsi);

                                    return values == null || values.size() != 1
                                            ? (Term) null
                                            : (Term) values.get(0);
                                }).filter(t -> t != null).findAny();

                        return maybeRHS.orElse(services.getTermBuilder().TRUE())
                                .equals(services.getTermBuilder().FALSE());
                    });

            if (!isFalseLsiPresent) {
                postconditionNodes.add(g.node());
            }
            else {
                preservedNodes.add(g.node());
            }
        }
    }

    /**
     * Returns the {@link PosInOccurrence} of the {@link SequentFormula} in the
     * given node which had the SE term label before (or still has it). Returns
     * an empty {@link Optional} is it could not be found.
     *
     * @param node
     *            The node to retrieve the {@link PosInOccurrence} from.
     * @return The {@link PosInOccurrence} of the {@link SequentFormula} in the
     *         given node which has / had the SE term label.
     */
    private Optional<PosInOccurrence> getPioOfFormulaWhichHadSELabel(
            Node node) {
        Node currNode = node;
        int pos = -1;

        while (!currNode.root() && pos == -1) {
            int i = 0;
            for (SequentFormula sf : currNode.sequent().succedent()) {
                if (SymbolicExecutionUtil
                        .hasSymbolicExecutionLabel(sf.formula())) {
                    pos = i;
                    break;
                }

                i++;
            }

            currNode = currNode.parent();
        }

        if (pos == -1) {
            return Optional.empty();
        }

        final ImmutableList<SequentFormula> succList = node.sequent()
                .succedent().asList();
        final SequentFormula updPostCondSeqFor = succList.take(pos).head();
        final PosInOccurrence proofOblPio = new PosInOccurrence(
                updPostCondSeqFor, PosInTerm.getTopLevel(), false);

        return Optional.of(proofOblPio);
    }

    /**
     * @return The {@link ProgramMethod} designated by the information provided
     *         to the constructor.
     */
    private ProgramMethod findMethod() {
        final List<KeYJavaType> declaredTypes = seIf.getDeclaredTypes();

        assert declaredTypes
                .size() > 0 : "Unexpectedly, no type is declared in the supplied Java file.";

        final List<ClassDeclaration> matchingClassDecls = declaredTypes.stream()
                .filter(t -> t.getJavaType().getFullName().equals(className))
                .filter(t -> t.getJavaType() instanceof ClassDeclaration)
                .map(t -> (ClassDeclaration) t.getJavaType())
                .collect(Collectors.toList());

        if (matchingClassDecls.isEmpty()) {
            final String errorMsg = GeneralUtilities.format(
                    "Could not find type %s in class %s", className,
                    file.getName());
            LOGGER.error(errorMsg);
            throw new RuntimeException(errorMsg);
        }

        assert matchingClassDecls
                .size() == 1 : "There should be only one type of a given name";

        final List<ProgramMethod> matchingMethods = GeneralUtilities
                .toStream(matchingClassDecls.get(0).getMembers())
                .filter(m -> m instanceof ProgramMethod)
                .map(m -> (ProgramMethod) m)
                .filter(m -> m.getName().equals(methodName))
                .filter(m -> JavaTypeInterface.getMethodTypeDescriptor(m)
                        .equals(methodTypeStr))
                .collect(Collectors.toList());

        if (matchingMethods.isEmpty()) {
            final String errorMsg = GeneralUtilities.format(
                    "Could not find method %s%s in class %s", methodName,
                    methodTypeStr, className);
            LOGGER.error(errorMsg);
            throw new RuntimeException(errorMsg);
        }

        assert matchingMethods
                .size() == 1 : "There should be only one method of a given signature";

        final ProgramMethod method = matchingMethods.get(0);
        return method;
    }

    /**
     * Parses a method identifier string; see
     * {@link #Analyzer(File, String, Optional)} for comments on the format.
     *
     * @param methodStr
     *            The string to parse.
     * @return true iff the parsing succeeded, false otherwise.
     */
    private boolean parseMethodString(String methodStr) {
        // @ formatter:off
        // Expected format:
        //
        // <fully qualified type name>::<method name>(<arg decl>)<return type
        // decl>
        //
        // where <arg decl> is according to the field descriptors
        // in the JVM specification, for instance
        //
        // [ILjava.lang.Object;D
        //
        // for an integer array, an Object and a double (not that
        // we would support doubles...). <return type decl> is
        // constructed similarly, only for a single type.
        // @ formatter:on

        final Pattern p = Pattern
                .compile("^([^:]*)::([^\\(]*)(\\([^\\)]*\\).*)$");
        final Matcher m = p.matcher(methodStr);

        if (!m.matches() || m.groupCount() != 3) {
            return false;
        }

        className = m.group(1);
        methodName = m.group(2);
        methodTypeStr = m.group(3);

        return true;
    }

    /**
     * Pretty prints an {@link AnalyzerResult} to the given {@link PrintStream},
     * e.g. System.out.
     *
     * @param result
     *            The {@link AnalyzerResult} to print.
     * @param ps
     *            The {@link PrintStream} used as an output.
     */
    public static void printResults(AnalyzerResult result, PrintStream ps) {
        if (result.unclosedLoopInvPreservedGoals() > 0) {
            // @formatter:off
            ps.println(String.format(
                    "============================================\n"
                  + "Open \"invariant preserved\" branches: **%s**:\n"
                  + "============================================\n",
                    result.unclosedLoopInvPreservedGoals()));
            // @formatter:on
        }

        if (result.unclosedPostCondSatisfiedGoals() > 0) {
            // @formatter:off
            ps.println(String.format(
                    "===================================================\n"
                  + "Open \"post condition satisfied\" branches: **%s**:\n"
                  + "===================================================\n",
                    result.unclosedPostCondSatisfiedGoals()));
            // @formatter:on
        }

        if (result.problematicExceptions().size() > 0) {
            // @formatter:off
            ps.println("=====================\n"
                    + "Unhandled Exceptions:\n"
                    + "=====================\n");
            // @formatter:on

            final PrintStream fPs = ps;
            result.problematicExceptions().forEach(e -> {
                fPs.println(e);
                fPs.println();
            });
        }

        if (result.numUncoveredFacts() > 0) {
            // @formatter:off
            ps.println("================\n"
                     + "Uncovered Facts:\n"
                     + "================\n");
            // @formatter:on

            final PrintStream fPs = ps;
            result.getUncoveredFacts().forEach(f -> {
                fPs.println(f);
                fPs.println();
            });
        }

        if (result.numAbstractlyCoveredFacts() > 0) {
            // @formatter:off
            ps.println("=========================\n"
                     + "Abstractly Covered Facts:\n"
                     + "=========================\n");
            // @formatter:on

            final PrintStream fPs = ps;
            result.getAbstractlyCoveredFacts().forEach(f -> {
                fPs.println(f);
                fPs.println();
            });
        }

        // @formatter:off
        ps.println("========\n"
                 + "Summary:\n"
                 + "========\n");
        // @formatter:on

        ps.printf(
                "Covered %s (%s concretely, %s abstractly) out of %s facts\n"
                        + "Strength:          %.2f%%\n"
                        + "Concrete Strength: %.2f%%\n",
                result.numCoveredFacts() + result.numAbstractlyCoveredFacts(),
                result.numCoveredFacts(), result.numAbstractlyCoveredFacts(),
                result.numFacts(), result.strength(),
                result.coveredStrength());
    }

    /**
     * Result of extracting {@link Fact}s from a {@link Proof} tree.
     *
     * @author Dominic Steinhoefel
     */
    private static class FactExtractionResult {
        /**
         * @see #getFacts()
         */
        private final List<Fact> facts;

        /**
         * @see #getUnclosedLoopInvPreservedGoals()
         */
        private final int unclosedLoopInvPreservedGoals;

        /**
         * @see #getUnclosedPostCondSatisfiedGoals()
         */
        private final int unclosedPostCondSatisfiedGoals;

        /**
         * Constructor.
         *
         * @param facts
         * @param unclosedExceptionGoals
         */
        public FactExtractionResult(List<Fact> facts,
                int unclosedExceptionGoals,
                int unclosedPostCondSatisfiedGoals) {
            this.facts = facts;
            this.unclosedLoopInvPreservedGoals = unclosedExceptionGoals;
            this.unclosedPostCondSatisfiedGoals =
                    unclosedPostCondSatisfiedGoals;
        }

        /**
         * @return the facts
         */
        public List<Fact> getFacts() {
            return facts;
        }

        /**
         * @return the number of unclosed "loop inv preserved" goals
         */
        public int getUnclosedLoopInvPreservedGoals() {
            return unclosedLoopInvPreservedGoals;
        }

        /**
         * @return the number of unclosed "post condition satisfied" goals
         */
        public int getUnclosedPostCondSatisfiedGoals() {
            return unclosedPostCondSatisfiedGoals;
        }

    }

    /**
     * A visitor for checking whether a given {@link RuleApp} type is present in
     * a {@link Proof} tree.
     *
     * @author Dominic Steinhoefel
     */
    private static class RuleAppVisitor implements ProofVisitor {
        /**
         * See {@link #success()}.
         */
        private boolean success = false;

        /**
         * The {@link RuleApp} {@link Class} type to search for.
         */
        private Class<? extends RuleApp> toSearch;

        /**
         * @param toSearch
         *            The {@link RuleApp} {@link Class} type to search for.
         */
        public RuleAppVisitor(Class<? extends RuleApp> toSearch) {
            this.toSearch = toSearch;
        }

        @Override
        public void visit(Proof proof, Node visitedNode) {
            if (visitedNode.getAppliedRuleApp() != null
                    && toSearch.isInstance(visitedNode.getAppliedRuleApp())) {
                success = true;
            }
        }

        /**
         * @return true iff the {@link RuleApp} type was found.
         */
        public boolean success() {
            return success;
        }
    }

    /**
     * Types of extracted {@link Fact}s.
     *
     * @author Dominic Steinhoefel
     */
    public static enum FactType {
        /** Loop body fact, i.e. an equation of the preserved part. */
        LOOP_BODY_FACT,

        /**
         * Post condition fact, i.e. a part of the final state after method
         * execution that should be shown using the post condition.
         */
        POST_COND_FACT
    }

    /**
     * A fact is a piece of knowledge about a final state or a specification
     * element which should be shown. A fact can be "covered" or "abstractly
     * covered"; for each of those cases, it contains a {@link Node} that should
     * be used for checking which is the case.
     *
     * @author Dominic Steinhoefel
     */
    public static class Fact {
        /**
         * Concise description of the fact, e.g. a (better short) formula.
         */
        private final String descr;

        /**
         * A {@link String} describing the path condition for this fact.
         */
        private final String pathCond;

        /**
         * The {@link FactType} of this {@link Fact}.
         */
        private final FactType factType;

        /**
         * The {@link Node} that indicates the {@link Fact} is covered if it can
         * be closed.
         */
        private final Node factCoveredNode;

        /**
         * The {@link Node} that indicates the {@link Fact} is abstractly
         * covered if it can be closed.
         */
        private final Node factAbstractlyCoveredNode;

        /**
         * The {@link Node} that indicates the {@link Fact} is indeed abstractly
         * covered, i.e. that the factAbstractlyCoveredNode cannot only be
         * closed because of the path condition implying the spec (this node has
         * to remain open).
         */
        private final Node factAbstractlyCoveredTestNode;

        /**
         * True iff the fact is covered.
         */
        private boolean covered = false;

        /**
         * True iff the fact is not covered, but abstractly covered.
         */
        private boolean abstractlyCovered = false;

        /**
         * Constructor. Sets all the final fields, i.e. all but covered and
         * abstractlyCovered.
         *
         * @param descr
         *            Concise description of the fact, e.g. a (better short)
         *            formula.
         * @param pathCond
         *            A {@link String} describing the path condition for this
         *            fact.
         * @param factType
         *            The {@link FactType} of this {@link Fact}.
         * @param factCoveredNode
         *            The {@link Node} that indicates the {@link Fact} is
         *            covered if it can be closed.
         * @param factAbstractlyCoveredNode
         *            The {@link Node} that indicates the {@link Fact} is
         *            abstractly covered if it can be closed.
         * @param factAbstractlyCoveredTestNode
         *            The {@link Node} that indicates the {@link Fact} is indeed
         *            abstractly covered, i.e. that the
         *            factAbstractlyCoveredNode cannot only be closed because of
         *            the path condition implying the spec (this node has to
         *            remain open).
         */
        public Fact(String descr, String pathCond, FactType factType,
                Node factCoveredNode, Node factAbstractlyCoveredNode,
                Node factAbstractlyCoveredTestNode) {
            this.descr = descr.trim();
            this.pathCond = pathCond.trim().replaceAll("<<[^>]*?>>", "");
            this.factType = factType;
            this.factCoveredNode = factCoveredNode;
            this.factAbstractlyCoveredNode = factAbstractlyCoveredNode;
            this.factAbstractlyCoveredTestNode = factAbstractlyCoveredTestNode;
        }

        /**
         * @return true iff the fact has been set to "covered".
         */
        public boolean isCovered() {
            return covered;
        }

        /**
         * Sets the "covered" flag of this {@link Fact}.
         *
         * @param covered
         *            true iff the {@link Fact} should be marked as "covered".
         */
        public void setCovered(boolean covered) {
            assert !abstractlyCovered || !covered;

            this.covered = covered;
        }

        /**
         * @return @return true iff the fact has been set to "abstractly
         *         covered".
         */
        public boolean isAbstractlyCovered() {
            return abstractlyCovered;
        }

        /**
         * Sets the "abstractly covered" flag of this {@link Fact}.
         *
         * @param abstractlyCovered
         *            true iff the {@link Fact} should be marked as "abstractly
         *            covered".
         */
        public void setAbstractlyCovered(boolean abstractlyCovered) {
            assert !abstractlyCovered || !covered;

            this.abstractlyCovered = abstractlyCovered;
        }

        public String getDescr() {
            return descr;
        }

        public String getPathCond() {
            return pathCond;
        }

        public FactType getFactType() {
            return factType;
        }

        public Node getFactCoveredNode() {
            return factCoveredNode;
        }

        public Node getFactAbstractlyCoveredNode() {
            return factAbstractlyCoveredNode;
        }

        public Node getFactAbstractlyCoveredTestNode() {
            return factAbstractlyCoveredTestNode;
        }

        @Override
        public String toString() {
            return String.format("%s, Path condition \"%s\"\n%s",
                    factTypeToString(factType), pathCond, descr);
        }

        private static String factTypeToString(FactType ft) {
            switch (ft) {
            case LOOP_BODY_FACT:
                return "Loop body fact";
            case POST_COND_FACT:
                return "Post condition implies final state fact";
            default:
                GeneralUtilities.logErrorAndThrowRTE(//
                        LOGGER, "Unknown fact type: %s", ft);
                return null;
            }
        }
    }

    /**
     * Represents an exception branch that could not be closed.
     *
     * @author Dominic Steinhoefel
     */
    public static class ExceptionResult {
        /**
         * A description of the exception, e.g. "Array Index out ouf Bounds".
         */
        private final String excLabel;

        /**
         * The path condition of the exception branch.
         */
        private final String pathCondition;

        /**
         * Constructor.
         *
         * @param excLabel
         *            A description of the exception, e.g. "Array Index out ouf
         *            Bounds".
         * @param pathCondition
         *            The path condition of the exception branch.
         */
        public ExceptionResult(String excLabel, String pathCondition) {
            this.excLabel = excLabel;
            this.pathCondition = pathCondition;
        }

        public String getExcLabel() {
            return excLabel;
        }

        public String getPathCondition() {
            return pathCondition;
        }

        @Override
        public String toString() {
            return String.format(
                    "Unclosed exception node \"%s\"\nPath condition: \"%s\"",
                    excLabel, pathCondition);
        }
    }

    /**
     * Result of a strength analysis as returned by {@link Analyzer#analyze()}.
     *
     * @author Dominic Steinhoefel
     */
    public static class AnalyzerResult {
        /**
         * A weight for "abstractly covered" facts.
         */
        private static final double ABSTRACTLY_COVERED_WEIGHT = 0.5d;

        /**
         * {@link List} of covered {@link Fact}s.
         */
        private final List<Fact> coveredFacts;

        /**
         * {@link List} of abstractly covered {@link Fact}s.
         */
        private final List<Fact> abstractlyCoveredFacts;

        /**
         * {@link List} of uncovered {@link Fact}s.
         */
        private final List<Fact> uncoveredFacts;

        /**
         * The number of loop invariant "preserved" goals that couldn't be
         * closed.
         */
        private final int unclosedLoopInvPreservedGoals;

        /**
         * The number of "post condition satisfied" goals that couldn't be
         * closed.
         */
        private final int unclosedPostCondSatisfiedGoals;

        /**
         * A {@link List} of {@link ExceptionResult}s for exception branches
         * that couldn't be closed.
         */
        private final List<ExceptionResult> problematicExceptions;

        /**
         * Constructor.
         *
         * @param coveredFacts
         *            See {@link #coveredFacts}
         * @param abstractlyCoveredFacts
         *            See {@link #abstractlyCoveredFacts}
         * @param unCoveredFacts
         *            See {@link #unCoveredFacts}
         * @param problematicExceptions
         *            See {@link #problematicExceptions}
         * @param unclosedLoopInvPreservedGoals
         *            See {@link #unclosedLoopInvPreservedGoals}
         * @param unclosedPostCondSatisfiedGoals
         *            See {@link #unclosedPostCondSatisfiedGoals}
         */
        public AnalyzerResult(List<Fact> coveredFacts,
                List<Fact> abstractlyCoveredFacts, List<Fact> unCoveredFacts,
                List<ExceptionResult> problematicExceptions,
                int unclosedLoopInvPreservedGoals,
                int unclosedPostCondSatisfiedGoals) {
            this.coveredFacts = coveredFacts;
            this.abstractlyCoveredFacts = abstractlyCoveredFacts;
            this.uncoveredFacts = unCoveredFacts;
            this.unclosedLoopInvPreservedGoals = unclosedLoopInvPreservedGoals;
            this.problematicExceptions = problematicExceptions;
            this.unclosedPostCondSatisfiedGoals =
                    unclosedPostCondSatisfiedGoals;
        }

        public List<Fact> getCoveredFacts() {
            return coveredFacts;
        }

        public List<Fact> getAbstractlyCoveredFacts() {
            return abstractlyCoveredFacts;
        }

        public List<Fact> getUncoveredFacts() {
            return uncoveredFacts;
        }

        /**
         * Returns the covered {@link Fact}s of {@link FactType} type.
         *
         * @param type
         *            The type of {@link Fact}s to retrieve.
         * @return The covered {@link Fact}s of {@link FactType} type.
         */
        public List<Fact> getCoveredFactsOfType(FactType type) {
            return coveredFacts.stream().filter(f -> f.factType == type)
                    .collect(Collectors.toList());
        }

        /**
         * Returns the abstractly covered {@link Fact}s of {@link FactType}
         * type.
         *
         * @param type
         *            The type of {@link Fact}s to retrieve.
         * @return The abstractly covered {@link Fact}s of {@link FactType}
         *         type.
         */
        public List<Fact> getAbstractlyCoveredFactsOfType(FactType type) {
            return abstractlyCoveredFacts.stream()
                    .filter(f -> f.factType == type)
                    .collect(Collectors.toList());
        }

        /**
         * Returns the uncovered {@link Fact}s of {@link FactType} type.
         *
         * @param type
         *            The type of {@link Fact}s to retrieve.
         * @return The uncovered {@link Fact}s of {@link FactType} type.
         */
        public List<Fact> getUncoveredFactsOfType(FactType type) {
            return uncoveredFacts.stream().filter(f -> f.factType == type)
                    .collect(Collectors.toList());
        }

        /**
         * @return The number of covered {@link Fact}s.
         */
        public int numCoveredFacts() {
            return coveredFacts.size();
        }

        /**
         * @return The number of abstractly covered {@link Fact}s.
         */
        public int numAbstractlyCoveredFacts() {
            return abstractlyCoveredFacts.size();
        }

        /**
         * @return The number of uncovered {@link Fact}s.
         */
        public int numUncoveredFacts() {
            return uncoveredFacts.size();
        }

        /**
         * @return The total number of {@link Fact}s.
         */
        public int numFacts() {
            return numCoveredFacts() + numAbstractlyCoveredFacts()
                    + numUncoveredFacts();
        }

        /**
         * @return A {@link List} of {@link ExceptionResult}s for exception
         *         branches that couldn't be closed.
         */
        public List<ExceptionResult> problematicExceptions() {
            return problematicExceptions;
        }

        /**
         * @return The number of loop invariant "preserved" goals that couldn't
         *         be closed.
         */
        public int unclosedLoopInvPreservedGoals() {
            return unclosedLoopInvPreservedGoals;
        }

        /**
         * @return The number of "post condition satisfied" goals that couldn't
         *         be closed.
         */
        public int unclosedPostCondSatisfiedGoals() {
            return unclosedPostCondSatisfiedGoals;
        }

        /**
         * @return The strength of this {@link AnalyzerResult} as a percentage
         *         value. Includes abstractly covered facts that are weighted by
         *         {@link #ABSTRACTLY_COVERED_WEIGHT}.
         */
        public double strength() {
            return 100d
                    * (((double) numCoveredFacts())
                            + ((double) numAbstractlyCoveredFacts())
                                    * ABSTRACTLY_COVERED_WEIGHT)
                    / ((double) numFacts());
        }

        /**
         * @return A strength value <b>without</b> the "abstractly covered"
         *         facts.
         */
        public double coveredStrength() {
            return 100d * ((double) numCoveredFacts()) / ((double) numFacts());
        }
    }

}
