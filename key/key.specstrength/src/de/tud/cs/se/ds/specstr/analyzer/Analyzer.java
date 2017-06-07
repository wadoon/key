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

import de.tud.cs.se.ds.specstr.rule.AnalyzeInvImpliesLoopEffectsRule;
import de.tud.cs.se.ds.specstr.rule.AnalyzePostCondImpliesMethodEffectsRule;
import de.tud.cs.se.ds.specstr.rule.StrengthAnalysisUtilities;
import de.tud.cs.se.ds.specstr.util.InformationExtraction;
import de.tud.cs.se.ds.specstr.util.Utilities;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.macros.FullPropositionalExpansionMacro;
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
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

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
            final String errorMsg = Utilities
                    .format("Error in parsing method descriptor %s", method);
            logger.error(errorMsg);
            throw new RuntimeException(errorMsg);
        }

        try {
            this.seIf = new SymbExInterface(file);
        } catch (ProblemLoaderException e) {
            Utilities.logErrorAndThrowRTE(logger,
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
            final Optional<SequentFormula> maybeWhileSeqFor = StrengthAnalysisUtilities
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

            // TODO: If we add the SET predicate also to the analysis goals, we
            // can apply try-close to get rid of irrelevant goals. This is about
            // those that have "false" in the post condition, there, "false &
            // SETAccumulate(...)" will still be false and closable.

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

        List<Fact> coveredFacts = new ArrayList<>();
        List<Fact> unCoveredFacts = new ArrayList<>();

        for (Fact fact : facts) {
            logger.trace("Proving fact %s", fact.descr);
            final Node factNode = fact.goal.node();
            seIf.applyMacro(new TryCloseMacro(10000), factNode);
            if (factNode.isClosed()) {
                coveredFacts.add(fact);
            } else {
                unCoveredFacts.add(fact);
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

        return new AnalyzerResult(coveredFacts, unCoveredFacts);
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

        // Apply OSS and propositional simplification to the open goals of
        // the post condition "facts"
        final List<Node> obsoleteUseCaseNodes = new ArrayList<>();
        final List<Node> newUseCaseNodes = new ArrayList<>();

        useCaseNodes.stream().map(n -> new Pair<Node, List<SequentFormula>>( //
                n, //
                StrengthAnalysisUtilities.toStream(n.sequent()).filter(
                        f -> f.formula().op() instanceof UpdateApplication)
                        .collect(Collectors.toList())))
                .filter(p -> !p.second.isEmpty()) //
                .forEach(p -> {
                    p.second.forEach(sf -> proof.getSubtreeGoals(p.first).head()
                            .apply(MiscTools.findOneStepSimplifier(proof)
                                    .createApp(
                                            findInSequent(sf,
                                                    p.first.sequent()),
                                            services)));

                    // Note: Will simplify only for nodes with update
                    // applications, but we assume that after symb ex all
                    // relevant nodes in any case have update applications
                    // left over
                    proof.getSubtreeGoals(p.first)
                            .forEach(g -> seIf.applyMacro(
                                    new FullPropositionalExpansionMacro(),
                                    g.node()));

                    if (!proof.isGoal(p.first)) {
                        obsoleteUseCaseNodes.add(p.first);
                        newUseCaseNodes.addAll(StrengthAnalysisUtilities
                                .toStream(proof.getSubtreeGoals(p.first))
                                .map(g -> g.node())
                                .collect(Collectors.toList()));
                    }
                });

        useCaseNodes.removeAll(obsoleteUseCaseNodes);
        useCaseNodes.addAll(newUseCaseNodes);

        facts.addAll(useCaseNodes.stream().map(n -> new Fact(
                polishFactDescription(n.sequent(), preservesAndUCNode.sequent(),
                        services),
                extractReadablePathCondition(proof.getSubtreeGoals(n).head()),
                FactType.LOOP_USE_CASE_FACT, proof.getGoal(n)))
                .collect(Collectors.toList()));
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

            if (AnalyzePostCondImpliesMethodEffectsRule.INSTANCE.isApplicable( //
                    g, maybePio.get())) {
                g.apply(AnalyzePostCondImpliesMethodEffectsRule.INSTANCE
                        .createApp(maybePio.get(), proof.getServices()));

                boolean first = true;
                for (Goal analysisGoal : g.proof()
                        .getSubtreeGoals(postCondNode)) {
                    if (first) {
                        first = false;
                        continue;
                    }

                    extractReadablePathCondition(analysisGoal);

                    final String branchLabel = analysisGoal.node().getNodeInfo()
                            .getBranchLabel();
                    facts.add(new Fact(branchLabel.split("\"")[1],
                            extractReadablePathCondition(analysisGoal),
                            branchLabel.contains("invariant fact")
                                    ? FactType.POST_COND_INV_FACT
                                    : FactType.POST_COND_FACT,
                            analysisGoal));
                }
            }
        }
    }

    /**
     * TODO
     * 
     * @param analysisGoal
     * @return
     */
    private static String extractReadablePathCondition(Goal analysisGoal) {
        String pathCond = "";
        try {
            boolean problem = false;
            Term pathCondTerm = analysisGoal.proof().getServices()
                    .getTermBuilder().tt();

            try {
                pathCondTerm = SymbolicExecutionUtil
                        .computePathCondition(analysisGoal.node(), true, true);
            } catch (RuntimeException e1) {
                problem = true;
            }

            pathCond = (problem ? "ERROR-PC " : "") + LogicPrinter
                    .quickPrintTerm(pathCondTerm,
                            analysisGoal.proof().getServices())
                    .replaceAll("(\\r|\\n|\\r\\n)+", " ");
        } catch (ProofInputException e) {
            logger.error("Couldn't compute path comdition for goal %s"
                    + analysisGoal.node().serialNr());
        }

        return pathCond;
    }

    /**
     * TODO
     * 
     * @param factSeq
     * @param originSeq
     * @param services
     * @return
     */
    private static String polishFactDescription(Sequent factSeq,
            Sequent originSeq, Services services) {
        final List<SequentFormula> newAntec = StrengthAnalysisUtilities
                .toStream(factSeq.antecedent()).collect(Collectors.toList());
        newAntec.removeAll(StrengthAnalysisUtilities
                .toStream(originSeq.antecedent()).collect(Collectors.toList()));

        final List<SequentFormula> newSucc = StrengthAnalysisUtilities
                .toStream(factSeq.succedent()).collect(Collectors.toList());
        newSucc.removeAll(StrengthAnalysisUtilities
                .toStream(originSeq.succedent()).collect(Collectors.toList()));

        Sequent newSequent = Sequent.EMPTY_SEQUENT;
        for (SequentFormula antecF : newAntec) {
            newSequent = newSequent.addFormula(antecF, true, false).sequent();
        }
        for (SequentFormula antecF : newSucc) {
            newSequent = newSequent.addFormula(antecF, false, false).sequent();
        }

        return LogicPrinter.quickPrintSequent(newSequent, services);
    }

    /**
     * TODO
     * 
     * @param sf
     * @param seq
     * @return
     */
    private static PosInOccurrence findInSequent(SequentFormula sf,
            Sequent seq) {
        for (SequentFormula otherSf : seq.antecedent()) {
            if (otherSf.formula().equals(sf.formula())) {
                return new PosInOccurrence(sf, PosInTerm.getTopLevel(), true);
            }
        }

        for (SequentFormula otherSf : seq.succedent()) {
            if (otherSf.formula().equals(sf.formula())) {
                return new PosInOccurrence(sf, PosInTerm.getTopLevel(), false);
            }
        }

        return null;
    }

    /**
     * TODO
     * 
     * @param proof
     * @param services
     * @param preservesAndUCNode
     * @param preservedNodes
     * @param useCaseNodes
     */
    private void extractPreservedAndUseCaseNodes(final Proof proof,
            final Node preservesAndUCNode, final List<Node> preservedNodes,
            final List<Node> useCaseNodes) {
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

            Optional<Term> rhs = StrengthAnalysisUtilities
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
                    useCaseNodes.add(g.node());
                } else if (op == services.getTermBuilder().FALSE().op()) {
                    preservedNodes.add(g.node());
                } else {
                    Utilities.logErrorAndThrowRTE(logger,
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

            final Goal[] preservedGoals = proof.getSubtreeGoals(preservedNode)
                    .head().apply(app).toArray(Goal.class);
            for (int i = 0; i < preservedGoals.length - 1; i++) {
                facts.add(new Fact(
                        preservedGoals[i].node().getNodeInfo().getBranchLabel()
                                .split("\"")[1],
                        extractReadablePathCondition(preservedGoals[i]),
                        FactType.LOOP_BODY_FACT, preservedGoals[i]));
            }

            final Node actualPreservedNode = preservedGoals[preservedGoals.length
                    - 1].node();
            seIf.applyMacro(new TryCloseMacro(10000),
                    preservedGoals[preservedGoals.length - 1].node());
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
     * @param preservedNode
     * @return
     */
    private Optional<PosInOccurrence> getPioOfFormulaWhichHadSELabel(
            Node preservedNode) {
        int pos = -1;
        {
            int i = 0;
            for (SequentFormula sf : preservedNode.parent().sequent()
                    .succedent()) {
                if (SymbolicExecutionUtil
                        .hasSymbolicExecutionLabel(sf.formula())) {
                    pos = i;
                    break;
                }

                i++;
            }
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
            final String errorMsg = Utilities.format(
                    "Could not find type %s in class %s", className,
                    file.getName());
            logger.error(errorMsg);
            throw new RuntimeException(errorMsg);
        }

        assert declaredTypes
                .size() == 1 : "There should be only one type of a given name";

        final List<ProgramMethod> matchingMethods = StrengthAnalysisUtilities
                .toStream(matchingClassDecls.get(0).getMembers())
                .filter(m -> m instanceof ProgramMethod)
                .map(m -> (ProgramMethod) m)
                .filter(m -> m.getName().equals(methodName))
                .filter(m -> InformationExtraction.getMethodTypeDescriptor(m)
                        .equals(methodTypeStr))
                .collect(Collectors.toList());

        if (matchingMethods.isEmpty()) {
            final String errorMsg = Utilities.format(
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

        Pattern p = Pattern.compile("^([^:]*)::([^\\(]*)(\\([^\\)]*\\).*)$");
        Matcher m = p.matcher(methodStr);

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

        ps.printf("Covered %s out of %s facts; Strength: %.2f%%\n",
                result.numCoveredFacts(), result.numFacts(),
                100d * ((double) result.numCoveredFacts())
                        / ((double) result.numFacts()));
    }

    public static enum FactType {
        LOOP_BODY_FACT, LOOP_USE_CASE_FACT, POST_COND_FACT, POST_COND_INV_FACT
    }

    public static class Fact {
        private final String descr;
        private final String pathCond;
        private final FactType factType;
        private final int goalNr;
        private final Goal goal;
        private boolean covered = false;

        public Fact(String descr, String pathCond, FactType factType,
                Goal goal) {
            this.descr = descr;
            this.pathCond = pathCond;
            this.factType = factType;
            this.goalNr = goal.node().serialNr();
            this.goal = goal;
        }

        public boolean isCovered() {
            return covered;
        }

        public void setCovered(boolean covered) {
            this.covered = covered;
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

        public int getGoalNr() {
            return goalNr;
        }

        public Goal getGoal() {
            return goal;
        }

        @Override
        public String toString() {
            return String.format("%s at goal %s\n%s\nPath condition: %s",
                    factTypeToString(factType), goalNr, descr, pathCond);
        }

        private static String factTypeToString(FactType ft) {
            switch (ft) {
            case LOOP_BODY_FACT:
                return "Loop body fact";
            case LOOP_USE_CASE_FACT:
                return "Loop use case fact";
            case POST_COND_FACT:
                return "Post condition implies final state fact";
            case POST_COND_INV_FACT:
                return "Post condition (WP) implies invariant fact";
            default:
                Utilities.logErrorAndThrowRTE( //
                        logger, "Unknown fact type: %s", ft);
                return null;
            }
        }
    }

    public static class AnalyzerResult {
        private final List<Fact> coveredFacts;
        private final List<Fact> uncoveredFacts;

        public AnalyzerResult(List<Fact> coveredFacts,
                List<Fact> unCoveredFacts) {
            this.coveredFacts = coveredFacts;
            this.uncoveredFacts = unCoveredFacts;
        }

        public List<Fact> getCoveredFacts() {
            return coveredFacts;
        }

        public List<Fact> getUncoveredFacts() {
            return uncoveredFacts;
        }

        public List<Fact> getCoveredFactsOfType(FactType type) {
            return coveredFacts.stream().filter(f -> f.factType == type)
                    .collect(Collectors.toList());
        }

        public List<Fact> getUncoveredFactsOfType(FactType type) {
            return uncoveredFacts.stream().filter(f -> f.factType == type)
                    .collect(Collectors.toList());
        }

        public int numCoveredFacts() {
            return coveredFacts.size();
        }

        public int numUncoveredFacts() {
            return uncoveredFacts.size();
        }

        public int numFacts() {
            return numCoveredFacts() + numUncoveredFacts();
        }
    }

}
