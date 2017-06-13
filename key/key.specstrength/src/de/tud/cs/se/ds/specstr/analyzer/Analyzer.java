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
import java.util.List;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.tud.cs.se.ds.specstr.rule.AbstractAnalysisRule;
import de.tud.cs.se.ds.specstr.rule.AnalyzeInvImpliesLoopEffectsRule;
import de.tud.cs.se.ds.specstr.rule.AnalyzePostCondImpliesMethodEffectsRule;
import de.tud.cs.se.ds.specstr.rule.AnalyzeUseCaseRule;
import de.tud.cs.se.ds.specstr.rule.FactAnalysisRule;
import de.tud.cs.se.ds.specstr.util.GeneralUtilities;
import de.tud.cs.se.ds.specstr.util.JavaTypeInterface;
import de.tud.cs.se.ds.specstr.util.LogicUtilities;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * TODO
 *
 * @author Dominic Steinhöfel
 */
public class Analyzer {
    private static final Logger logger = LogManager.getFormatterLogger();

    private File file;
    private String className, methodName, methodTypeStr;
    private SymbExInterface seIf;
    private Optional<File> outProofFile;

    /**
     * TODO
     * 
     * @param file
     * @param method
     * @param outProofFile
     * @throws ProblemLoaderException
     */
    public Analyzer(File file, String method, Optional<File> outProofFile) {
        this.file = file;
        if (!parseMethodString(method)) {
            final String errorMsg = GeneralUtilities
                    .format("Error in parsing method descriptor %s", method);
            logger.error(errorMsg);
            throw new RuntimeException(errorMsg);
        }

        try {
            this.seIf = new SymbExInterface(file);
        } catch (ProblemLoaderException e) {
            GeneralUtilities.logErrorAndThrowRTE(logger,
                    "ProblemLoaderException occurred while loading file %s\nMessage:\n%s",
                    file.getName(), e.getMessage());
        }
        this.outProofFile = outProofFile;
    }

    /**
     * TODO
     * 
     * @return
     */
    public AnalyzerResult analyze() {
        logger.info("Analyzing Java file %s", file);

        final ProgramMethod method = findMethod();

        logger.info("Analyzing method %s::%s%s", className, methodName,
                methodTypeStr);

        // Run until while loop
        final Optional<Goal> maybeWhileGoal = seIf
                .finishSEUntilLoopOrEnd(method);
        final Proof proof = seIf.proof();

        final List<Node> postConditionNodes = new ArrayList<>();
        final List<Fact> facts = new ArrayList<>();

        Node useCasePredecessor = proof.root();

        if (maybeWhileGoal.isPresent()) {
            final Goal whileGoal = maybeWhileGoal.get();
            final Node whileNode = whileGoal.node();

            // Apply loop invariant rule
            final Optional<SequentFormula> maybeWhileSeqFor = GeneralUtilities
                    .toStream(whileGoal.node().sequent().succedent())
                    .filter(f -> SymbolicExecutionUtil
                            .hasSymbolicExecutionLabel(f.formula()))
                    .filter(f -> JavaTools.getActiveStatement(
                            TermBuilder.goBelowUpdates(f.formula())
                                    .javaBlock()) instanceof While)
                    .findFirst();

            assert maybeWhileSeqFor.isPresent();

            final SequentFormula whileSeqFor = maybeWhileSeqFor.get();

            final PosInOccurrence whilePio = new PosInOccurrence(whileSeqFor,
                    PosInTerm.getTopLevel(), false);

            final RuleApp loopInvRuleApp = LoopScopeInvariantRule.INSTANCE
                    .createApp(whilePio, whileGoal.proof().getServices())
                    .tryToInstantiate(whileGoal);

            whileGoal.apply(loopInvRuleApp);

            // Try to close first open goal ("initially valid")
            seIf.applyMacro(new TryCloseMacro(1000), whileNode.child(0));

            if (!whileNode.child(0).isClosed()) {
                logger.warn("The loop's invariant is not initially valid");
            }

            // Finish symbolic execution preserved & use case goal
            final Node preservesAndUCNode = whileNode.child(1);
            seIf.finishSEForNode(preservesAndUCNode);

            // Post condition facts. Those have to be extracted *before* the use
            // case facts, since the goals might change that are analyzed for
            // the use case
            extractPostCondFacts(proof, facts);

            // Find "preserves" and "use case" branches
            final List<Node> preservedNodes = new ArrayList<>();

            extractPreservedAndUseCaseNodes(proof, preservesAndUCNode,
                    preservedNodes, postConditionNodes);

            // Loop facts
            extractLoopBodyFactsAndShowValidity( //
                    proof, preservedNodes, facts);
            extractUseCaseFacts(proof, useCasePredecessor, postConditionNodes,
                    facts);

            useCasePredecessor = preservesAndUCNode;
        } else {
            // Post condition facts
            extractPostCondFacts(proof, facts);
        }

        logger.info("Collected %s facts", facts.size());

        logger.info("Proving facts, this may take some time...");

        // The show-the-facts loop

        List<Fact> coveredFacts = new ArrayList<>();
        List<Fact> abstractlyCoveredFacts = new ArrayList<>();
        List<Fact> unCoveredFacts = new ArrayList<>();

        for (Fact fact : facts) {
            logger.trace("Proving fact %s", fact.descr);

            final Node factNode = fact.factCoveredNode;
            seIf.applyMacro(new TryCloseMacro(10000), factNode);

            if (factNode.isClosed()) {
                logger.trace("Fact covered");
                coveredFacts.add(fact);
            } else {
                final Node abstractlyCoveredNode = fact.factAbstractlyCoveredNode;

                boolean abstractlyCovered = false;
                if (abstractlyCoveredNode != null) {
                    seIf.applyMacro(new TryCloseMacro(10000),
                            abstractlyCoveredNode);
                    abstractlyCovered = abstractlyCoveredNode.isClosed();
                }

                if (abstractlyCovered) {
                    logger.trace("Fact abstractly covered");
                    abstractlyCoveredFacts.add(fact);
                } else {
                    logger.trace("Fact uncovered");
                    unCoveredFacts.add(fact);
                }
            }
        }

        logger.trace("Done proving facts.");

        if (outProofFile.isPresent()) {
            try {
                logger.info("Writing proof to file %s", outProofFile.get());
                proof.saveToFile(outProofFile.get());
            } catch (IOException e) {
                logger.error("Problem writing proof to file %s, message:\n%s",
                        outProofFile.get(), e.getMessage());
            }
        }

        logger.trace("Finished analysis of Java file %s", file);

        return new AnalyzerResult(coveredFacts, abstractlyCoveredFacts,
                unCoveredFacts);
    }

    /**
     * TODO
     * 
     * @param proof
     * @param preservesAndUCNode
     * @param useCaseNodes
     * @param facts
     * @param services
     */
    private void extractUseCaseFacts(final Proof proof, Node preservesAndUCNode,
            final List<Node> useCaseNodes, final List<Fact> facts) {
        final Services services = proof.getServices();

        useCaseNodes.removeIf(n -> !n.getNodeInfo().getBranchLabel().equals(
                AbstractAnalysisRule.POSTCONDITION_SATISFIED_BRANCH_LABEL));

        for (final Node n : useCaseNodes) {
            final String readablePathCond = extractReadablePathCondition(
                    n.parent());

            final Node newNode = LogicUtilities.quickSimplifyUpdates(n);

            final Optional<PosInOccurrence> maybePioOfApplySeqFor = //
                    getPioOfFormulaWhichHadSELabel(newNode);
            assert maybePioOfApplySeqFor.isPresent();

            final List<Node> factNodes = GeneralUtilities
                    .toStream(proof.getGoal(newNode)
                            .apply(AnalyzeUseCaseRule.INSTANCE.createApp(
                                    maybePioOfApplySeqFor.get(), services)))
                    .map(g -> g.node()).collect(Collectors.toList());

            for (final Node factNode : factNodes) {
                final Iterable<Node> factAnalysisNodes = //
                        GeneralUtilities.toStream(proof.getGoal(factNode)
                                .apply(FactAnalysisRule.INSTANCE.createApp(null,
                                        proof.getServices())))
                                .map(g -> g.node())
                                .collect(Collectors.toList());

                if (factCanBeDiscarded(factAnalysisNodes)) {
                    // Discard the fact -- too easy ;)
                    continue;
                }
                
                final String branchLabel = factNode.getNodeInfo()
                        .getBranchLabel();

                facts.add(new Fact(branchLabel.split("\"")[1],
                        readablePathCond, FactType.LOOP_USE_CASE_FACT,
                        FactAnalysisRule.getFactCoveredNode(factAnalysisNodes),
                        null));
            }
        }
    }

    /**
     * TODO
     * 
     * @param proof
     * @param facts
     */
    private void extractPostCondFacts(Proof proof, List<Fact> facts) {
        for (Goal g : proof.openGoals()) {
            final Node postCondNode = g.node();
            final Optional<PosInOccurrence> maybePio = //
                    getPioOfFormulaWhichHadSELabel(postCondNode);

            if (!maybePio.isPresent()) {
                continue;
            }

            if (!AnalyzePostCondImpliesMethodEffectsRule.INSTANCE.isApplicable( //
                    g, maybePio.get())) {
                continue;
            }

            final Iterable<Node> analysisNodes = //
                    GeneralUtilities
                            .toStream(
                                    g.apply(AnalyzePostCondImpliesMethodEffectsRule.INSTANCE
                                            .createApp(maybePio.get(),
                                                    proof.getServices())))
                            .map(goal -> goal.node())
                            .collect(Collectors.toList());

            for (Node analysisNode : analysisNodes) {
                if (!analysisNode.getNodeInfo().getBranchLabel().equals(
                        AbstractAnalysisRule.POSTCONDITION_SATISFIED_BRANCH_LABEL)) {

                    final String readablePathCond = extractReadablePathCondition(
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
                                    factAnalysisNodes)));
                }
            }
        }
    }

    /**
     * TODO
     * 
     * @param proof
     * @param services
     * @param preservedNodes
     * @param facts
     */
    private void extractLoopBodyFactsAndShowValidity(final Proof proof,
            final List<Node> preservedNodes, final List<Fact> facts) {
        final Services services = proof.getServices();

        int invariantGoalsNotPreserved = 0;

        for (Node preservedNode : preservedNodes) {
            final Optional<PosInOccurrence> proofOblPio = getPioOfFormulaWhichHadSELabel(
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
                    .filter(n -> !n.getNodeInfo().getBranchLabel()
                            .equals(AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL))
                    .collect(Collectors.toList());

            for (Node analysisNode : analysisNodes) {
                final String branchLabel = analysisNode.getNodeInfo()
                        .getBranchLabel();
                final String readablePathCondition = extractReadablePathCondition(
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
                        FactAnalysisRule.getFactAbstractlyCoveredNode(
                                factAnalysisNodes)));
            }

            final Optional<Node> maybeActualPreservedNode = GeneralUtilities
                    .toStream(analysisNodesImmList).map(goal -> goal.node())
                    .filter(n -> n.getNodeInfo().getBranchLabel() != null
                            && n.getNodeInfo().getBranchLabel()
                                    .equals(AbstractAnalysisRule.INVARIANT_PRESERVED_BRANCH_LABEL))
                    .findAny();
            assert maybeActualPreservedNode.isPresent();

            final Node actualPreservedNode = maybeActualPreservedNode.get();
            seIf.applyMacro(new TryCloseMacro(10000), actualPreservedNode);
            if (!actualPreservedNode.isClosed()) {
                invariantGoalsNotPreserved++;
            }
        }

        if (invariantGoalsNotPreserved > 0) {
            logger.warn(
                    "Loop invariant could be invalid: %s open preserves goals",
                    invariantGoalsNotPreserved);
        }
    }

    /**
     * TODO
     * 
     * @param analysisGoals
     * @return
     */
    private boolean factCanBeDiscarded(Iterable<Node> analysisGoals) {
        // Discard the fact if it can be proven without the
        // specification
        final Node coveredByTrueNode = FactAnalysisRule
                .getCoveredByTrueNode(analysisGoals);
        seIf.applyMacro(new TryCloseMacro(1000), coveredByTrueNode);

        return coveredByTrueNode.isClosed();
    }

    /**
     * TODO
     * 
     * @param analysisNode
     * @return
     */
    private static String extractReadablePathCondition(Node analysisNode) {
        String pathCond = "";
        try {
            boolean problem = false;
            Term pathCondTerm = analysisNode.proof().getServices()
                    .getTermBuilder().tt();

            try {
                pathCondTerm = SymbolicExecutionUtil
                        .computePathCondition(analysisNode, true, true);
            } catch (RuntimeException e1) {
                problem = true;
            }

            pathCond = (problem ? "ERROR-PC " : "") + LogicPrinter
                    .quickPrintTerm(pathCondTerm,
                            analysisNode.proof().getServices())
                    .replaceAll("(\\r|\\n|\\r\\n)+", " ");
        } catch (ProofInputException e) {
            logger.error("Couldn't compute path comdition for goal %s"
                    + analysisNode.serialNr());
        }

        return pathCond;
    }

    /**
     * TODO
     * 
     * @param proof
     * @param services
     * @param preservesAndUCNode
     * @param preservedNodes
     * @param postconditionNodes
     */
    private void extractPreservedAndUseCaseNodes(final Proof proof,
            final Node preservesAndUCNode, final List<Node> preservedNodes,
            final List<Node> postconditionNodes) {
        final Services services = proof.getServices();
        final LocationVariable loopScopeIndex = SymbExInterface
                .findLoopScopeIndex(proof, preservesAndUCNode);

        for (Goal g : proof.getSubtreeGoals(preservesAndUCNode)) {
            if (g.node().parent().getAppliedRuleApp()
                    .rule() == AnalyzePostCondImpliesMethodEffectsRule.INSTANCE
                    && g != proof.getSubtreeGoals(g.node().parent()).head()) {
                // We ignore the goals for the strength analysis of post
                // conditions; only the first one after such a rule app will be
                // considered.
                continue;
            }

            final Optional<Term> rhs = GeneralUtilities
                    .toStream(g.node().sequent().succedent())
                    .map(sf -> sf.formula())
                    .filter(f -> f.op() instanceof UpdateApplication).map(f -> {
                        ImmutableArray<Term> values = SymbolicExecutionUtil
                                .extractValueFromUpdate(f.sub(0),
                                        loopScopeIndex);

                        return values == null || values.size() != 1
                                ? (Term) null : (Term) values.get(0);
                    }).filter(t -> t != null).findAny();

            if (rhs.isPresent()) {
                final Operator op = rhs.get().op();
                if (op == services.getTermBuilder().TRUE().op()) {
                    postconditionNodes.add(g.node());
                } else if (op == services.getTermBuilder().FALSE().op()) {
                    preservedNodes.add(g.node());
                } else {
                    GeneralUtilities.logErrorAndThrowRTE(logger,
                            "Unexpected (not simplified?) value for loop scope index %s in goal %s: %s",
                            loopScopeIndex, g.node().serialNr(), rhs);
                }
            } else {
                logger.trace(
                        "Couldn't find the value for loop scope index %s in goal #%s",
                        loopScopeIndex, g.node().serialNr());
            }
        }
    }

    /**
     * TODO
     * 
     * @param preservedNode
     * @return
     */
    private Optional<PosInOccurrence> getPioOfFormulaWhichHadSELabel(
            Node preservedNode) {
        Node currNode = preservedNode;
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

        final ImmutableList<SequentFormula> succList = preservedNode.sequent()
                .succedent().asList();
        final SequentFormula updPostCondSeqFor = succList.take(pos).head();
        final PosInOccurrence proofOblPio = new PosInOccurrence(
                updPostCondSeqFor, PosInTerm.getTopLevel(), false);

        return Optional.of(proofOblPio);
    }

    /**
     * TODO
     * 
     * @return
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
            logger.error(errorMsg);
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
            logger.error(errorMsg);
            throw new RuntimeException(errorMsg);
        }

        assert matchingMethods
                .size() == 1 : "There should be only one method of a given signature";

        final ProgramMethod method = matchingMethods.get(0);
        return method;
    }

    /**
     * TODO
     * 
     * @param methodStr
     * @return
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
     * TODO
     * 
     * @param result
     * @param ps
     */
    public static void printResults(AnalyzerResult result, PrintStream ps) {
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

        ps.printf(
                "Covered %s (%s completely, %s abstractly) out of %s facts; Strength: %.2f%%\n",
                result.numCoveredFacts() + result.numAbstractlyCoveredFacts(),
                result.numCoveredFacts(), result.numAbstractlyCoveredFacts(),
                result.numFacts(), result.strength());
    }

    public static enum FactType {
        LOOP_BODY_FACT, LOOP_USE_CASE_FACT, POST_COND_FACT
    }

    public static class Fact {
        private final String descr;
        private final String pathCond;
        private final FactType factType;
        private final int nodeNr;
        private final int abstractlyCoveredNodeNr;
        private final Node factCoveredNode;
        private final Node factAbstractlyCoveredNode;
        private boolean covered = false;
        private boolean abstractlyCovered = false;

        public Fact(String descr, String pathCond, FactType factType,
                Node factCoveredNode, Node factAbstractlyCoveredNode) {
            this.descr = descr;
            this.pathCond = pathCond;
            this.factType = factType;
            this.factCoveredNode = factCoveredNode;
            this.nodeNr = factCoveredNode.serialNr();
            this.factAbstractlyCoveredNode = factAbstractlyCoveredNode;
            this.abstractlyCoveredNodeNr = factAbstractlyCoveredNode == null
                    ? -1 : factAbstractlyCoveredNode.serialNr();
        }

        public boolean isCovered() {
            return covered;
        }

        public void setCovered(boolean covered) {
            assert !abstractlyCovered || !covered;

            this.covered = covered;
        }

        public boolean isAbstractlyCovered() {
            return abstractlyCovered;
        }

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

        public int getFactCoveredNodeNr() {
            return nodeNr;
        }

        public Node getFactCoveredNode() {
            return factCoveredNode;
        }

        public int getFactAbstractlyCoveredNodeNr() {
            return abstractlyCoveredNodeNr;
        }

        public Node getFactAbstractlyCoveredNode() {
            return factAbstractlyCoveredNode;
        }

        @Override
        public String toString() {
            return String.format("%s: Goal #%s, Path condition \"%s\"\n%s",
                    factTypeToString(factType), nodeNr, pathCond.trim(), descr);
        }

        private static String factTypeToString(FactType ft) {
            switch (ft) {
            case LOOP_BODY_FACT:
                return "Loop body fact";
            case LOOP_USE_CASE_FACT:
                return "Loop use case fact";
            case POST_COND_FACT:
                return "Post condition implies final state fact";
            default:
                GeneralUtilities.logErrorAndThrowRTE( //
                        logger, "Unknown fact type: %s", ft);
                return null;
            }
        }
    }

    public static class AnalyzerResult {
        private final List<Fact> coveredFacts;
        private final List<Fact> abstractlyCoveredFacts;
        private final List<Fact> uncoveredFacts;

        public AnalyzerResult(List<Fact> coveredFacts,
                List<Fact> abstractlyCoveredFacts, List<Fact> unCoveredFacts) {
            this.coveredFacts = coveredFacts;
            this.abstractlyCoveredFacts = abstractlyCoveredFacts;
            this.uncoveredFacts = unCoveredFacts;
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

        public List<Fact> getCoveredFactsOfType(FactType type) {
            return coveredFacts.stream().filter(f -> f.factType == type)
                    .collect(Collectors.toList());
        }

        public List<Fact> getAbstractlyCoveredFactsOfType(FactType type) {
            return abstractlyCoveredFacts.stream()
                    .filter(f -> f.factType == type)
                    .collect(Collectors.toList());
        }

        public List<Fact> getUncoveredFactsOfType(FactType type) {
            return uncoveredFacts.stream().filter(f -> f.factType == type)
                    .collect(Collectors.toList());
        }

        public int numCoveredFacts() {
            return coveredFacts.size();
        }

        public int numAbstractlyCoveredFacts() {
            return abstractlyCoveredFacts.size();
        }

        public int numUncoveredFacts() {
            return uncoveredFacts.size();
        }

        public int numFacts() {
            return numCoveredFacts() + numAbstractlyCoveredFacts()
                    + numUncoveredFacts();
        }

        public double strength() {
            return 100d
                    * (((double) numCoveredFacts())
                            + ((double) numAbstractlyCoveredFacts()) * 0.5d)
                    / ((double) numFacts());
        }
    }

}
