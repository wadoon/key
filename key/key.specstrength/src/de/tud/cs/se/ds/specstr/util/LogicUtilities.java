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

package de.tud.cs.se.ds.specstr.util;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.tud.cs.se.ds.specstr.logic.label.StrengthAnalysisParameterlessTL;
import de.tud.cs.se.ds.specstr.rule.AbstractAnalysisRule;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.util.LinkedHashMap;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * TODO
 *
 * @author Dominic Steinhoefel
 */
public final class LogicUtilities {

    /**
     * A cache for formulas that are known to originate from a loop invariant.
     */
    private static final Map<Node, Set<Term>> LOOP_INV_FORMULAS_CACHE =
            new LinkedHashMap<>();

    private LogicUtilities() {
        // Hidden constructor -- it's a utility class.
    }

    /**
     * Extracts the store terms of the heap {@link Term} origHeapTerm and
     * returns them along with the inner heap {@link Term}, which is a constant
     * or a heap with a top level anon operation.
     *
     * @param services
     *            The {@link Services} object.
     * @param origHeapTerm
     *            The heap {@link Term} to analyze.
     * @return A pair of the inner heap in origHeapTerm and the stores around
     *         the inner heap.
     */
    public static Optional<Pair<Term, List<Term>>> extractStoreEqsAndInnerHeapTerm(
            Services services, final Term origHeapTerm) {
        if (origHeapTerm == null) {
            return Optional.empty();
        }

        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();

        final List<Term> storeEqualities = new ArrayList<>();
        Term innerHeapTerm = origHeapTerm;

        // TODO: Is it justified to assume that a heap is of the form
        // store(store(...(anon/heap...))), i.e. if there is a store,
        // then we have a store sequence at the beginning?
        Term currHeapTerm = innerHeapTerm;
        while (currHeapTerm.op() == heapLDT.getStore()) {
            final Term targetObj = currHeapTerm.sub(1);
            final Term field = currHeapTerm.sub(2);
            final Term value = currHeapTerm.sub(3);

            // Note: value could contain method-local variables, in which
            // case the fact is likely to be uncovered by the post
            // condition. Still, we don't remove it, since then indeed, this
            // reflects behavior that is not shown to the outside, and thus
            // indicates that we're not using the strongest possible post
            // condition.

            final Sort sort = getHeapStoreTargetSort(services, currHeapTerm);

            storeEqualities.add(tb.equals(
                    tb.select(sort, tb.getBaseHeap(), targetObj, field),
                    value));

            currHeapTerm = currHeapTerm.sub(0);
        }

        // Here, currHeapTerm should be the "core" without any stores.
        innerHeapTerm = currHeapTerm;

        return Optional
                .of(new Pair<Term, List<Term>>(innerHeapTerm, storeEqualities));
    }

    /**
     * Gets the sort of a "store" expression, that is the sort of the stored
     * value. Also works for null-assignments and Array types.
     *
     * @param services
     *            The {@link Services} object for {@link NamespaceSet}s and
     *            {@link JavaInfo}.
     * @param currHeapTerm
     *            The heap store {@link Term}.
     * @return The sort of the store expression.
     */
    private static Sort getHeapStoreTargetSort(final Services services,
            final Term currHeapTerm) {
        final Term targetObj = currHeapTerm.sub(1);
        final Term field = currHeapTerm.sub(2);
        final Term value = currHeapTerm.sub(3);

        Sort sort = null;
        if (!(value.sort() instanceof NullSort)) {
            sort = value.sort();
        }
        else if (((ProgramVariable) targetObj.op()).getKeYJavaType()
                .getJavaType() instanceof ArrayDeclaration) {
            sort = services.getNamespaces().sorts().lookup(
                    ((ArrayDeclaration) ((ProgramVariable) targetObj.op())
                            .getKeYJavaType().getJavaType()).getBaseType()
                                    .getName());
        }
        else {
            sort = services.getJavaInfo().getAttribute(
                    // Format is "path.to.type::$field"; we have to remove the
                    // "$"
                    // to find the field in the JavaInfo.
                    field.toString().replaceAll("\\$", ""),
                    services.getJavaInfo()
                            .getTypeByClassName(
                                    field.toString().split("::")[0]))
                    .sort();
        }
        return sort;
    }

    /**
     * Returns the {@link FunctionalOperationContract} underlying the current
     * {@link Proof}.
     *
     * @param services
     *            The {@link Services} object of the {@link Proof}.
     * @return The {@link FunctionalOperationContract} underlying the current
     *         {@link Proof}.
     */
    public static FunctionalOperationContract getFOContract(Services services) {
        final ContractPO contractPO = services.getSpecificationRepository()
                .getContractPOForProof(services.getProof());
        assert contractPO != null
                && contractPO instanceof FunctionalOperationContractPO;
        final FunctionalOperationContract fContract = //
                ((FunctionalOperationContractPO) contractPO).getContract();
        return fContract;
    }

    /**
     * Extracts all loop scope indices from the given {@link PosInOccurrence},
     * if possible; otherwise, returns an empty {@link Set}.
     *
     * @param pio
     *            The {@link PosInOccurrence} that maybe contains one or more
     *            loop scope indices
     * @param services
     *            The {@link Services} object.
     * @return The {@link Set} of all loop scope indices.
     * @see LoopScopeInvariantRule
     * @see ParameterlessTermLabel#LOOP_SCOPE_INDEX_LABEL
     */
    public static List<LocationVariable> retrieveLoopScopeIndices(
            PosInOccurrence pio, Services services) {
        final LoopScopeIndexVisitor visitor = new LoopScopeIndexVisitor();
        // Preorder walking makes sure that the "outer" loop scope index is
        // visited first.
        final Term formula = TermBuilder.goBelowUpdates(pio.subTerm());
        formula.execPreOrder(visitor);
        return visitor.getLoopScopeIndeces();
    }

    /**
     * @see #prepareGoal(PosInOccurrence, Goal, Term, String, TermLabelState,
     *      Rule)
     *
     * @param pio
     *            The {@link PosInOccurrence} to remove.
     * @param analysisGoal
     *            The analysis {@link Goal} with which to work.
     * @param fact
     *            The fact {@link Term} to add.
     * @param termLabelState
     *            The {@link TermLabelState} for the ongoing rule application.
     * @param rule
     *            The {@link Rule} of the current rule application; needed for
     *            the {@link TermLabel} stuff.
     */
    public static void prepareGoal(final PosInOccurrence pio,
            final Goal analysisGoal, final Term fact,
            TermLabelState termLabelState, Rule rule) {
        prepareGoal(pio, analysisGoal, fact,
                AbstractAnalysisRule.COVERS_FACT_BRANCH_LABEL_PREFIX,
                termLabelState, rule);
    }

    /**
     * Prepares a {@link Goal} for strength analysis:
     * <ul>
     * <li>Sets the branch label of the {@link Goal} according to the given fact
     * {@link Term}</li>
     * <li>Removes the given {@link PosInOccurrence} from the
     * {@link Sequent}</li>
     * <li>Adds the fact {@link Term} to the succedent</li>
     * <li>Adds a {@link StrengthAnalysisParameterlessTL#FACT_LABEL}
     * {@link TermLabel} to the fact {@link Term}</li>
     * </ul>
     *
     * @param pio
     *            The {@link PosInOccurrence} to remove.
     * @param analysisGoal
     *            The analysis {@link Goal} with which to work.
     * @param fact
     *            The fact {@link Term} to add.
     * @param descr
     *            The prefix description for the branch label, e.g. "Covers
     *            fact" or whatever.
     * @param termLabelState
     *            The {@link TermLabelState} for the ongoing rule application.
     * @param rule
     *            The {@link Rule} of the current rule application; needed for
     *            the {@link TermLabel} stuff.
     */
    public static void prepareGoal(final PosInOccurrence pio,
            final Goal analysisGoal, final Term fact, final String descr,
            TermLabelState termLabelState, Rule rule) {
        final Services services = analysisGoal.proof().getServices();

        analysisGoal.setBranchLabel(String.format("%s \"%s\"", descr,
                LogicPrinter
                        .quickPrintTerm(TermBuilder.goBelowUpdates(fact),
                                services)
                        .replaceAll("(\\r|\\n|\\r\\n)+", "")
                        .replaceAll("<<[^>]+>>", "").trim()));

        analysisGoal.removeFormula(pio);

        Term newFormula = services.getTermBuilder().label(fact,
                StrengthAnalysisParameterlessTL.FACT_LABEL);
        newFormula = TermLabelManager.refactorTerm(termLabelState, services,
                null, newFormula, rule, analysisGoal,
                AbstractAnalysisRule.FACT_HINT, null);

        analysisGoal.addFormula(new SequentFormula(newFormula), false, true);
    }

    /**
     * Adds a precondition for a fact to the given {@link Goal}.
     *
     * @param analysisGoal
     *            The {@link Goal} to work with.
     * @param t
     *            The fact {@link Term} to add.
     * @param addFactPremiseLabel
     *            Signals whether the
     *            {@link StrengthAnalysisParameterlessTL#FACT_PREMISE_LABEL}
     *            should be added to t.
     * @param termLabelState
     *            The {@link TermLabelState} for the ongoing rule application.
     * @param rule
     *            The {@link Rule} of the current rule application; needed for
     *            the {@link TermLabel} stuff.
     */
    public static void addFactPrecondition(Goal analysisGoal, Term t,
            boolean addFactPremiseLabel, TermLabelState termLabelState,
            Rule rule) {
        Term newFormula = addFactPremiseLabel
                ? analysisGoal.proof().getServices().getTermBuilder().label(t,
                        StrengthAnalysisParameterlessTL.FACT_PREMISE_LABEL)
                : t;
        newFormula = TermLabelManager.refactorTerm(termLabelState,
                analysisGoal.proof().getServices(), null, newFormula, rule,
                analysisGoal, AbstractAnalysisRule.FACT_PREMISE_HINT, null);

        analysisGoal.addFormula(new SequentFormula(newFormula), true, false);
    }

    /**
     * Adds the given {@link Iterable} of premise {@link Term}s to the succedent
     * of the given {@link Goal}; labels those from index <code>0</code> to
     * <code>numFactsWithPremiseLabels - 1</code> with
     * {@link StrengthAnalysisParameterlessTL#FACT_PREMISE_LABEL}.
     *
     * @param analysisGoal
     *            The {@link Goal} to work with.
     * @param terms
     *            The premises to add.
     * @param numFactsWithPremiseLabels
     *            All facts from index <code>0</code> to
     *            <code>numFactsWithPremiseLabels - 1</code> will be labeled
     *            with
     *            {@link StrengthAnalysisParameterlessTL#FACT_PREMISE_LABEL}
     * @param termLabelState
     *            The {@link TermLabelState} for the ongoing rule application.
     * @param rule
     *            The {@link Rule} of the current rule application; needed for
     *            the {@link TermLabel} stuff.
     */
    public static void addFactPreconditions(//
            Goal analysisGoal, Iterable<Term> terms,
            int numFactsWithPremiseLabels, TermLabelState termLabelState,
            Rule rule) {

        int i = 0;
        for (Term term : terms) {
            addFactPrecondition(analysisGoal, term,
                    i < numFactsWithPremiseLabels, termLabelState, rule);
            i++;
        }
    }

    /**
     * Recursively tries to find the origin of the given formula {@link Term} by
     * getting the oldest {@link FormulaTermLabel} and finding the origin of
     * that.
     *
     * @param analysisGoal
     *            The {@link Goal} to start with.
     * @param formula
     *            The formula {@link Term} the origin of which is being looked
     *            for.
     * @return The {@link OriginOfFormula} for the given formula {@link Term}.
     */
    public static OriginOfFormula findOriginOfFormula(final Goal analysisGoal,
            final Term formula) {
        // First, retrieve all FormulaTermLabels
        final List<FormulaTermLabel> formulaTermLabels = //
                termLabelsOfType(formula, FormulaTermLabel.class);

        assert formulaTermLabels.size() > 0 : //
        "There should be <<F>> term labels in the invariant term";

        // Get the smallest term label, this should identify the origin
        Collections.sort(formulaTermLabels, (l1, l2) -> {
            if (l1.equals(l2)) {
                return 0;
            }

            final List<String> idsInFirst = getIDsOfFormulaTermLabel(l1);
            final List<String> idsInSecond = getIDsOfFormulaTermLabel(l2);
            final List<String> both = new ArrayList<>(idsInFirst);
            both.addAll(idsInSecond);
            Collections.sort(both);

            final String smallest = both.get(0);
            final int posResult = Integer.parseInt(smallest.split("\\.")[0]);
            if (idsInFirst.contains(smallest)) {
                return -posResult;
            }
            else {
                return posResult;
            }
        });
        final FormulaTermLabel smallest = formulaTermLabels.get(0);

        return findOriginOfTermLabel(analysisGoal, smallest);
    }

    /**
     * Extracts the open {@link Node}s that have a modality in the succedent
     * from the subtree of the given {@link Node}.
     *
     * @param node
     *            The root of the subtree to search.
     * @return The open {@link Node}s in the subtree of node that have a
     *         modality in the succedent.
     */
    public static List<Node> extractOpenNodesWithModality(Node node) {
        return GeneralUtilities.toStream(node.proof().getSubtreeGoals(node))
                .map(g -> g.node())
                .filter(n -> GeneralUtilities.toStream(n.sequent().succedent())
                        .anyMatch(
                                f -> f.formula().containsJavaBlockRecursive()))
                .collect(Collectors.toList());
    }

    /**
     * Removes the formulas from the antecedent of the given {@link Goal} which
     * are there because of the loop invariant.
     *
     * @param analysisGoal
     *            The {@link Goal} to remove loop invariant formulas form.
     * @param loopInvNode
     *            The loop invariant {@link Node} designating the invariant
     *            formulas to remove. May be null; in this case, all loop
     *            invariant formulas will be removed.
     */
    public static void removeLoopInvFormulasFromAntec(final Goal analysisGoal,
            Node loopInvNode) {
        assert loopInvNode == null || loopInvNode
                .getAppliedRuleApp() instanceof LoopInvariantBuiltInRuleApp : //
        "You should pass a node with a loop invariant application.";

        // We remove all partially instantiated no pos taclets, such as
        // replaceKnownAuxiliaryConstant, since otherwise, there could be
        // invariant formulas contained.

        // TODO: This could be refined, such as inserting all things that
        // taclets can insert and using the remaining procedure below to get rid
        // of invariant formulas.

        // XXX: Something goes wrong here. During the analysis, there are
        // obviously replaceKnownSelect taclets left that are applied; when
        // reloading with KeY, those taclets are however removed correctly. What
        // goes wrong here?
        analysisGoal.indexOfTaclets().removeTaclets(
                analysisGoal.indexOfTaclets().getPartialInstantiatedApps());

        for (SequentFormula sf : analysisGoal.sequent().antecedent()) {
            boolean remove = loopInvNode == null
                    ? LOOP_INV_FORMULAS_CACHE.values().stream()
                            .anyMatch(set -> set.contains(sf.formula()))
                    : LOOP_INV_FORMULAS_CACHE.containsKey(loopInvNode)
                            && LOOP_INV_FORMULAS_CACHE.get(loopInvNode)
                                    .contains(sf.formula());

            if (!remove && sf.formula().hasLabels()) {
                final LinkedHashSet<Term> sePreds = findSETPreds(sf.formula());
                if (!sePreds.isEmpty() && !sePreds.stream()
                        .noneMatch(pred -> sf.formula().equals(pred))) {
                    // We don't remove the SE predicate formula
                    continue;
                }
                
                if (termLabelsOfType(sf.formula(), FormulaTermLabel.class)
                        .isEmpty()) {
                    // This is probably a formula which only has been added
                    // during the application of the analysis goal, we
                    // definitely
                    // cannot trace it back. Ignore.
                    continue;
                }

                // Find origin of this label
                final OriginOfFormula origin = //
                        findOriginOfFormula(analysisGoal, sf.formula());

                final Node node = origin.getNode().parent();
                if ((loopInvNode == null
                        && node.getAppliedRuleApp() instanceof LoopInvariantBuiltInRuleApp)
                        || node.equals(loopInvNode)) {
                    remove = true;

                    // Add value to the cache
                    updateCache(sf.formula(), loopInvNode,
                            analysisGoal.proof().root());
                }
            }

            if (remove) {
                analysisGoal.removeFormula(
                        new PosInOccurrence(sf, PosInTerm.getTopLevel(), true));
            }
        }
    }

    /**
     * Updates the {@link #LOOP_INV_FORMULAS_CACHE} s.th. the {@link Term}
     * invFormula is listed as a loop invariant part of the given {@link Node}.
     * Either loopInvNode of fallbackNode must be non-null.
     *
     * @param invFormula
     *            The invariant formula to cache.
     * @param loopInvNode
     *            The loop invariant {@link Node}; may be null, in this case,
     *            the fallbackNode must be non-null.
     * @param fallbackNode
     *            The fallback {@link Node} to use as a key for the cache if
     *            loopInvNode is null.
     */
    private static void updateCache(final Term invFormula,
            final Node loopInvNode, final Node fallbackNode) {
        assert loopInvNode != null || fallbackNode != null;

        final Node insertNode = loopInvNode == null ? fallbackNode
                : loopInvNode;
        Set<Term> cacheSet = LOOP_INV_FORMULAS_CACHE.get(insertNode);
        if (cacheSet == null) {
            cacheSet = new LinkedHashSet<>();
            LOOP_INV_FORMULAS_CACHE.put(insertNode, cacheSet);
        }
        cacheSet.add(invFormula);
    }

    /**
     * Adds the SE predicate to the antecedent of the given {@link Goal} such
     * that it can be closed even with the SE predicate present in the
     * succedent.
     *
     * @param goal
     *            The {@link Goal} to add the SE predicate to.
     */
    public static void addSETPredicateToAntec(final Goal goal) {        
        final Optional<Pair<SequentFormula, LinkedHashSet<Term>>> maybeSETPredicates = //
                Stream.concat(
                        GeneralUtilities.toStream(goal.sequent().succedent()),
                        GeneralUtilities.toStream(goal.sequent().antecedent()))
                        .map(sf -> {
                            return new Pair<SequentFormula, LinkedHashSet<Term>>(sf,
                                    findSETPreds(sf.formula()));
                        }).filter(p -> !p.second.isEmpty()).findAny();

        if (!maybeSETPredicates.isPresent()) {
            // There are easy goals where the post condition is just "false", so
            // that should be OK
            return;
        }

        final Term seqFor = maybeSETPredicates.get().first.formula();
        final List<Term> updates = getUpdates(seqFor);
        
        final TermBuilder tb = goal.proof().getServices().getTermBuilder();

        Term newFormula = maybeSETPredicates.get().second.stream()
                .reduce(tb.tt(), (acc, elem) -> tb.and(acc, elem));
        
        for (int i = updates.size() - 1; i >= 0; i--) {
            newFormula = goal.proof().getServices().getTermBuilder()
                    .apply(updates.get(i), newFormula);
        }

        goal.addFormula(new SequentFormula(newFormula), true, false);
    }

    /**
     * Returns the list of updates in the {@link Term} t. t has to be an udpate
     * application.
     *
     * @param t
     *            The {@link UpdateApplication} {@link Term} to return the list
     *            of update terms for.
     * @return The list of updates in the {@link Term} t.
     */
    public static List<Term> getUpdates(Term t) {
        assert t.op() instanceof UpdateApplication : //
        "Can only extract updates from update apps, got: " + t.op();

        final List<Term> result = new ArrayList<>();
        while (t.op() instanceof UpdateApplication) {
            result.add(t.sub(0));
            t = t.sub(1);
        }

        return result;
    }

    /**
     * Transforms an update to a {@link Map} from left-hand-sides to
     * right-hand-sides.
     *
     * @param updateTerm
     *            The {@link Term} to transform.
     * @return A {@link Map} from update left-hand-sides to right-hand-sides.
     */
    public static LinkedHashMap<LocationVariable, Term> updateToMap(
            final Term updateTerm) {
        final LinkedHashMap<LocationVariable, Term> updateContent =
                StreamSupport.stream(//
                        MergeRuleUtils.getUpdateLeftSideLocations(updateTerm)
                                .spliterator(),
                        true).collect(
                                Collectors.toMap(lhs -> lhs,
                                        lhs -> MergeRuleUtils
                                                .getUpdateRightSideFor(
                                                        updateTerm, lhs),
                                        (u, v) -> {
                                            throw new IllegalStateException(
                                                    String.format(
                                                            "Duplicate key %s",
                                                            u));
                                        }, LinkedHashMap::new));
        return updateContent;
    }

    private static <L extends TermLabel> List<L> termLabelsOfType(
            final Term formula, Class<L> wanted) {
        final List<L> labels = new ArrayList<L>();

        formula.execPreOrder(new DefaultVisitor() {
            @Override
            public void visit(Term visited) {
                if (visited.hasLabels()) {
                    labels.addAll(GeneralUtilities.toStream(visited.getLabels())
                            .filter(l -> wanted.isInstance(l))
                            .map(l -> wanted.cast(l))
                            .collect(Collectors.toList()));
                }
            }
        });

        return labels;
    }

    private static Set<String> formulaTermLabelIDsDeep(Term t) {
        final Set<String> termLabelIDsInSeqFor = new LinkedHashSet<String>();

        t.execPreOrder(new DefaultVisitor() {
            @Override
            public void visit(Term visited) {
                if (visited.hasLabels()) {
                    termLabelIDsInSeqFor.addAll(formulaTermLabelIDs(visited));
                }
            }
        });

        return termLabelIDsInSeqFor;
    }

    /**
     * Recursively tries to find the origin of the given
     * {@link FormulaTermLabel}.
     *
     * @param analysisGoal
     *            The {@link Goal} to start with.
     * @param label
     *            The {@link FormulaTermLabel} the origin of which is being
     *            looked for.
     * @return An {@link OriginOfFormula} for the given
     *         {@link FormulaTermLabel}; elements of this object might be null
     *         if the origin is not found, which however should not happen if
     *         the given {@link Goal} is a sensible choice (i.e., the origin is
     *         in the tree above the {@link Goal}).
     */
    private static OriginOfFormula findOriginOfTermLabel(
            final Goal analysisGoal, final FormulaTermLabel label) {
        Node currNode = analysisGoal.node();
        SequentFormula originForm = null;

        while (!currNode.root()) {
            List<String> allLabelsInNode = new ArrayList<>();
            final Node parent = currNode.parent();
            for (SequentFormula oSf : parent.sequent()) {
                final Set<String> labelsInSeqFor = //
                        formulaTermLabelIDsDeep(oSf.formula());

                allLabelsInNode.addAll(labelsInSeqFor);
                if (labelsInSeqFor.contains(label.toString())) {
                    originForm = oSf;
                    break;
                }
            }

            final List<String> termLabelMajorIDsOfLabel = //
                    getIDsOfFormulaTermLabel(label).stream()
                            .map(s -> s.split("\\.")[0])
                            .collect(Collectors.toList());
            final List<String> termLabelMajorIDsInNode = //
                    allLabelsInNode.stream().map(s -> s.split("\\.")[0])
                            .collect(Collectors.toList());

            final long numMatches = termLabelMajorIDsOfLabel.stream()
                    .filter(s -> termLabelMajorIDsInNode.contains(s)).count();

            if (numMatches == 0) {
                break;
            }
            else {
                currNode = parent;
            }
        }

        return new OriginOfFormula(currNode, originForm);
    }

    private static List<String> formulaTermLabelIDs(Term t) {
        final List<String> result = new ArrayList<>();

        if (t.hasLabels()) {
            StreamSupport.stream(t.getLabels().spliterator(), true)
                    .filter(label -> (label instanceof FormulaTermLabel))
                    .map(label -> (FormulaTermLabel) label).forEach(label -> {
                        result.addAll(getIDsOfFormulaTermLabel(label));
                    });
        }

        return result;
    }

    private static List<String> getIDsOfFormulaTermLabel(FormulaTermLabel l) {
        final List<String> result = new ArrayList<>();

        result.add(l.getId());
        result.addAll(
                Arrays.stream(l.getBeforeIds()).collect(Collectors.toList()));

        return result;
    }

    /**
     * @param formula
     *            The formula to obtain the symbolic execution predicate from.
     * @return The set of SE predicate {@link Term}s.
     */
    private static LinkedHashSet<Term> findSETPreds(Term formula) {
        SETPredVisitor v = new SETPredVisitor();
        formula.execPostOrder(v);
        return v.getSetPredTerms();
    }

    /**
     * Determines the origin of a {@link SequentFormula} in terms of a
     * {@link Node} and the original {@link SequentFormula}.
     *
     * @author Dominic Steinhoefel
     */
    public static class OriginOfFormula {
        /**
         * The origin {@link Node}.
         */
        private final Node node;

        /**
         * The original {@link SequentFormula}.
         */
        private final SequentFormula seqFor;

        /**
         * Constructor.
         *
         * @param node
         *            See {@link #node}.
         * @param seqFor
         *            See {@link #seqFor}.
         */
        public OriginOfFormula(Node node, SequentFormula seqFor) {
            this.node = node;
            this.seqFor = seqFor;
        }

        public Node getNode() {
            return node;
        }

        public SequentFormula getSeqFor() {
            return seqFor;
        }
    }

    private static class SETPredVisitor extends DefaultVisitor {
        /**
         * The result of the {@link Visitor} execution.
         */
        private LinkedHashSet<Term> setPredTerms = new LinkedHashSet<>();

        @Override
        public void visit(Term visited) {
            if (visited.op().name().toString()
                    .startsWith(AbstractOperationPO.UNINTERPRETED_PREDICATE_NAME)) {
                setPredTerms.add(visited);
            }
        }

        public LinkedHashSet<Term> getSetPredTerms() {
            return setPredTerms;
        }
    }

    private static class LoopScopeIndexVisitor extends DefaultVisitor {
        /**
         * The result of the {@link Visitor} execution.
         */
        private List<LocationVariable> indices = new ArrayList<>();

        @Override
        public void visit(Term visited) {
            if (visited.op() instanceof LocationVariable && visited.hasLabels()
                    && visited.containsLabel(
                            ParameterlessTermLabel.LOOP_SCOPE_INDEX_LABEL)) {
                final LocationVariable lsi = (LocationVariable) visited.op();
                if (!indices.contains(lsi)) {
                    indices.add(lsi);
                }
            }
        }

        public List<LocationVariable> getLoopScopeIndeces() {
            return indices;
        }
    }

    /**
     * Finds the loop scope index {@link LocationVariable} in the given
     * {@link Node} that is assigned FALSE; determines the loop the preserved
     * part of which is being analyzed.
     * 
     * @param node
     *            The {@link Node} to find the loop scope index
     *            {@link LocationVariable} which is set to false.
     *
     * @return The loop scope index {@link LocationVariable} in the given
     *         {@link Node} that is assigned FALSE.
     */
    public static LocationVariable findLoopScopeIndexVar(Node node) {
        final Services services = node.proof().getServices();

        LocationVariable loopScopeIdxVar = null;

        for (SequentFormula sf : node.sequent().succedent()) {
            List<LocationVariable> maybeIdxVar = retrieveLoopScopeIndices(
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), false),
                    services);

            if (!maybeIdxVar.isEmpty()) {
                final List<LocationVariable> falseLSI = maybeIdxVar.stream()
                        .filter(lsi -> MergeRuleUtils
                                .getUpdateRightSideFor(sf.formula().sub(0), lsi)
                                .equals(services.getTermBuilder().FALSE()))
                        .collect(Collectors.toList());
                assert falseLSI
                        .size() == 1 : "There has to be exaclty one loop scope index that's set to false.";
                loopScopeIdxVar = falseLSI.get(0);
                break;
            }
        }

        return loopScopeIdxVar;
    }

    /**
     * Finds the {@link Node} where the given loop scope index has been
     * introduced. The returned node, if non-null (so it has been found, which
     * means that the inputs to the method make sense) has guaranteed a
     * {@link LoopInvariantBuiltInRuleApp} application.
     *
     * @param node
     *            The {@link Node} to start with; will search upwards in the
     *            {@link Proof} tree from there.
     * @param loopScopeIdxVar
     *            The loop scope index {@link LocationVariable} to find the
     *            introducing {@link Node} for.
     * @return The {@link Node} where the given loop scope index has been
     *         introduced, or null, if the inputs do not make sense (i.e., in
     *         the tree above node there is not the
     *         {@link LoopScopeInvariantRule} application that is being looked
     *         for).
     */
    public static Node findCorrespondingLoopInvNode(Node node,
            LocationVariable loopScopeIdxVar) {
        Node currNode = node.parent();
        boolean found = false;
        while (!currNode.root()) {
            if (currNode.getAppliedRuleApp()
                    .rule() == LoopScopeInvariantRule.INSTANCE
                    && !currNode.getLocalProgVars().contains(loopScopeIdxVar)) {

                found = true;
                break;

            }

            currNode = currNode.parent();
        }

        if (!found) {
            currNode = null;
        }
        return currNode;
    }

}
