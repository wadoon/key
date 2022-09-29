package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.proof.rulefilter.SetRuleFilter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.feature.findprefix.FindPrefixRestrictionFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.ClausesSmallerThanFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EliminableQuantifierTF;
import de.uka.ilkd.key.strategy.quantifierHeuristics.SplittableQuantifiedFormulaFeature;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termfeature.*;
import de.uka.ilkd.key.strategy.termgenerator.AllowedCutPositionsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;
import de.uka.ilkd.key.util.MiscTools;

import java.util.*;
import java.util.stream.Collectors;

public class SymbExOnlyStrategy extends AbstractFeatureStrategy {

    protected final StrategyProperties strategyProperties;

    private final ArithTermFeatures tf;
    private final FormulaTermFeatures ff;
    private final ValueTermFeature vf;

    private final Services services;

    private final Services getServices() {
        return services;
    };

    private final HeapLDT heapLDT;

    private static final Map<String, Integer> ADMITTED_RULESETS = Map.ofEntries(
        Map.entry("closure", -10000000),
        Map.entry("alpha", -1000000),
        Map.entry("concrete", -100000),
        Map.entry("simplify_prog", -10000),
        Map.entry("loop_scope_inv_taclet", -10000),
        Map.entry("simplify_autoname", -10000),
        Map.entry("split_if", -10000),
        Map.entry("split_cond", -10000),
        Map.entry("executeIntegerAssignment", -10000),
        Map.entry("simplify_expression", -10000),
        Map.entry("method_expand", -10000)
    );

    public SymbExOnlyStrategy(Proof proof,
                                 StrategyProperties strategyProperties) {
        super(proof);
        this.strategyProperties = (StrategyProperties) strategyProperties.clone();
        services = proof.getServices();

        heapLDT = getServices().getTypeConverter().getHeapLDT();

        this.tf = new ArithTermFeatures(getServices().getTypeConverter().getIntegerLDT());
        this.ff = new FormulaTermFeatures(this.tf);
        this.vf = new ValueTermFeature(op(heapLDT.getNull()));

    }

    @Override
    public Name name() {
        return new Name("Symbolic Execution Only");
    }

    @Override
    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return null;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return computeCost(app, pio, goal) != TopRuleAppCost.INSTANCE;
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        /*Feature tacletCost = inftyConst();
        if (app instanceof TacletApp) {
            TacletApp ta = ((TacletApp) app);
            for (RuleSet ruleSet : ta.taclet().getRuleSets()) {
                if (ADMITTED_RULESETS.contains(ruleSet.name().toString())) {
                    tacletCost = longConst(0);
                }
            }
        }*/

        if (app.rule().name().toString().equals("andLeft")) {
            if (pos.subTerm().getLabel(OriginTermLabel.NAME) != null
                && ((OriginTermLabel)pos.subTerm().getLabel(OriginTermLabel.NAME)).getSubtermOrigins().toString().contains("@")) {
                return inftyConst().computeCost(app, pos, goal);
            }
        }

        RuleFilter ruleSetFilter = rule -> {
            boolean admittedRule = false;
            if (rule instanceof Taclet) {
                Taclet t = (Taclet) rule;
                for (RuleSet rs : t.getRuleSets()) {
                    if (ADMITTED_RULESETS.containsKey(rs.name().toString())) {
                        admittedRule = true;
                    }
                }
            }
            return admittedRule || rule.equals(MiscTools.findOneStepSimplifier(getProof()));
        };

        RuleFilter ossFilter = rule -> rule.equals(MiscTools.findOneStepSimplifier(getProof()));

        Feature nestedConditionFeature = createFeatureFromAdmittedRuleSets();

        return ConditionalFeature.createConditional(ossFilter, longConst(-11000), nestedConditionFeature).computeCost(app, pos, goal);

        //final Feature oneStepSimplificationF = oneStepSimplificationFeature(longConst(-11000));
        /*
        return SumFeature.createSum(
            AutomatedRuleFeature.INSTANCE,
            NonDuplicateAppFeature.INSTANCE,
            AgeFeature.INSTANCE,
            f).computeCost(app, pos, goal);*/
    }

    private Feature createFeatureFromAdmittedRuleSets() {
        List<Map.Entry<String, Integer>> l = new ArrayList<>(ADMITTED_RULESETS.entrySet());
        return createFeatureFromAdmittedRuleSets(l, 0);
    }

    private Feature createFeatureFromAdmittedRuleSets(List<Map.Entry<String, Integer>> l, int startIndex) {
        RuleFilter ruleSetFilter = rule -> {
            if (rule instanceof Taclet) {
                Taclet t = (Taclet) rule;
                for (RuleSet rs : t.getRuleSets()) {
                    if (l.get(startIndex).getKey().equals(rs.name().toString())) {
                        return true;
                    }
                }
            }
            return false;
        };
        Map.Entry<String, Integer> entry = l.get(startIndex);
        if (startIndex == l.size() - 1) {
            //return longConst(l.get(startIndex).getValue());
            return ConditionalFeature.createConditional(ruleSetFilter, longConst(entry.getValue()), inftyConst());
        } else {

            Feature nested = createFeatureFromAdmittedRuleSets(l, startIndex + 1);
            return ConditionalFeature.createConditional(ruleSetFilter, longConst(entry.getValue()), nested);
        }
    }


    public RuleAppCost computeCostOld(RuleApp app, PosInOccurrence pos, Goal goal) {
        //Feature dispatcher = setupCostComputationF(goal.proof());
        Feature dispatcher = setupCostComputation(goal.proof());
        final Feature ifMatchedF = ifZero(MatchedIfFeature.INSTANCE, longConst(+1));

        final Feature methodSpecF;
        final String methProp = strategyProperties.getProperty(StrategyProperties.METHOD_OPTIONS_KEY);
        if (methProp.equals(StrategyProperties.METHOD_CONTRACT)) {
            methodSpecF = methodSpecFeature(longConst(-20));
        } else if (methProp.equals(StrategyProperties.METHOD_EXPAND)) {
            methodSpecF = methodSpecFeature(inftyConst());
        } else if (methProp.equals(StrategyProperties.METHOD_NONE)) {
            methodSpecF = methodSpecFeature(inftyConst());
        } else {
            methodSpecF = null;
            assert false;
        }

        final String queryProp = strategyProperties.getProperty(StrategyProperties.QUERY_OPTIONS_KEY);
        final Feature queryF;
        if (queryProp.equals(StrategyProperties.QUERY_ON)) {
            queryF = querySpecFeature(new QueryExpandCost(200, 1, 1, false));
        } else if (queryProp.equals(StrategyProperties.QUERY_RESTRICTED)) {
            // All tests in the example directory pass with this strategy.
            // Hence, the old query_on strategy is obsolete.
            queryF = querySpecFeature(new QueryExpandCost(500, 0, 1, true));
        } else if (queryProp.equals(StrategyProperties.QUERY_OFF)) {
            queryF = querySpecFeature(inftyConst());
        } else {
            queryF = null;
            assert false;
        }

        final Feature depSpecF;
        final String depProp = strategyProperties.getProperty(StrategyProperties.DEP_OPTIONS_KEY);
        final SetRuleFilter depFilter = new SetRuleFilter();
        depFilter.addRuleToSet(UseDependencyContractRule.INSTANCE);
        if (depProp.equals(StrategyProperties.DEP_ON)) {
            depSpecF = ConditionalFeature.createConditional(depFilter, longConst(250));
        } else {
            depSpecF = ConditionalFeature.createConditional(depFilter, inftyConst());
        }

        // NOTE (DS, 2019-04-10): The new loop-scope based rules are realized
        // as taclets. The strategy settings for those are handled further
        // down in this class.
        Feature loopInvF;
        final String loopProp = strategyProperties.getProperty(StrategyProperties.LOOP_OPTIONS_KEY);
        if (loopProp.equals(StrategyProperties.LOOP_INVARIANT)) {
            loopInvF = loopInvFeature(longConst(0));
            /* NOTE (DS, 2019-04-10): Deactivated the built-in loop scope rule
             * since we now have the loop scope taclets which are based on the
             * same theory, but offer several advantages. */
            //} else if (loopProp.equals(StrategyProperties.LOOP_SCOPE_INVARIANT)) {
            //    loopInvF = loopInvFeature(inftyConst(), longConst(0));
        } else {
            loopInvF = loopInvFeature(inftyConst());
        }

        final Feature blockFeature;
        final Feature loopBlockFeature;
        final Feature loopBlockApplyHeadFeature;
        final String blockProperty = strategyProperties.getProperty(StrategyProperties.BLOCK_OPTIONS_KEY);
        if (blockProperty.equals(StrategyProperties.BLOCK_CONTRACT_INTERNAL)) {
            blockFeature = blockContractInternalFeature(longConst(Long.MIN_VALUE));
            loopBlockFeature = loopContractInternalFeature(longConst(Long.MIN_VALUE));
            loopBlockApplyHeadFeature = loopContractApplyHead(longConst(Long.MIN_VALUE));
        } else if (blockProperty.equals(StrategyProperties.BLOCK_CONTRACT_EXTERNAL)) {
            blockFeature = blockContractExternalFeature(longConst(Long.MIN_VALUE));
            loopBlockFeature = SumFeature.createSum(
                loopContractExternalFeature(longConst(Long.MIN_VALUE)),
                loopContractInternalFeature(longConst(42)));
            loopBlockApplyHeadFeature = loopContractApplyHead(longConst(Long.MIN_VALUE));
        } else {
            blockFeature = blockContractInternalFeature(inftyConst());
            loopBlockFeature = loopContractExternalFeature(inftyConst());
            loopBlockApplyHeadFeature = loopContractApplyHead(inftyConst());
        }

        final Feature oneStepSimplificationF = oneStepSimplificationFeature(longConst(-11000));

        final Feature mergeRuleF;
        final String mpsProperty = strategyProperties.getProperty(StrategyProperties.MPS_OPTIONS_KEY);
        if (mpsProperty.equals(StrategyProperties.MPS_MERGE)) {
            mergeRuleF = mergeRuleFeature(longConst(-4000));
        } else {
            mergeRuleF = mergeRuleFeature(inftyConst());
        }

        // final Feature smtF = smtFeature(inftyConst());

        return SumFeature.createSum(
            AutomatedRuleFeature.INSTANCE,
            NonDuplicateAppFeature.INSTANCE,
            // splitF,
            // strengthenConstraints,
            AgeFeature.INSTANCE, oneStepSimplificationF, mergeRuleF,
            // smtF,
            methodSpecF, queryF, depSpecF, loopInvF, blockFeature, loopBlockFeature,
            loopBlockApplyHeadFeature,
            ifMatchedF, dispatcher).computeCost(app, pos, goal);
    }

    private Feature oneStepSimplificationFeature(Feature cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(MiscTools.findOneStepSimplifier(getProof()));
        return ConditionalFeature.createConditional(filter, cost);
    }

    private RuleSetDispatchFeature setupCostComputation(Proof proof) {
        RuleSetDispatchFeature d = new RuleSetDispatchFeature();

        bindRuleSet(d, "semantics_blasting", inftyConst());
        bindRuleSet(d, "simplify_heap_high_costs", inftyConst());
        bindRuleSet(d, "cut_direct", inftyConst());
        bindRuleSet(d, "concrete", add(longConst(-11000), ScaleFeature.createScaled(
                FindDepthFeature.INSTANCE, 10.0)));

        return d;
    }

    private RuleSetDispatchFeature setupCostComputationF(Proof proof) {
        final IntegerLDT numbers = proof.getServices().getTypeConverter().getIntegerLDT();
        final LocSetLDT locSetLDT = proof.getServices().getTypeConverter().getLocSetLDT();

        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();


        bindRuleSet(d, "semantics_blasting", inftyConst());
        bindRuleSet(d, "simplify_heap_high_costs", inftyConst());

        bindRuleSet(d, "closure", -15000);
        bindRuleSet(d, "alpha", -7000);
        bindRuleSet(d, "delta", -6000);
        bindRuleSet(d, "simplify_boolean", -200);

        bindRuleSet(
            d,
            "concrete",
            add(longConst(-11000), ScaleFeature.createScaled(
                FindDepthFeature.INSTANCE, 10.0)));
        /*
        bindRuleSet(d, "simplify", -4500);
        bindRuleSet(d, "simplify_enlarging", -2000);
        bindRuleSet(d, "simplify_ENLARGING", -1900);
        bindRuleSet(d, "simplify_expression", -100);
        bindRuleSet(d, "executeIntegerAssignment", -100);
        bindRuleSet(d, "simplify_int", inftyConst());

         */

        /*

        bindRuleSet(
            d,
            "javaIntegerSemantics",
            ifZero(sequentContainsNoPrograms(),
                longConst(-5000),
                ifZero(leq(CountBranchFeature.INSTANCE, longConst(1)),
                    longConst(-5000), inftyConst())));

        // always give infinite cost to obsolete rules
        bindRuleSet(d, "obsolete", inftyConst());

        // taclets for special invariant handling
        bindRuleSet(d, "loopInvariant", -20000);

        setupSelectSimplification(d);

        bindRuleSet(
            d,
            "no_self_application",
            ifZero(MatchedIfFeature.INSTANCE,
                NoSelfApplicationFeature.INSTANCE));

        bindRuleSet(
            d,
            "find_term_not_in_assumes",
            ifZero(MatchedIfFeature.INSTANCE,
                not(contains(AssumptionProjection.create(0),
                    FocusProjection.INSTANCE))));

        bindRuleSet(
            d,
            "update_elim",
            add(longConst(-8000), ScaleFeature.createScaled(
                FindDepthFeature.INSTANCE, 10.0)));
        bindRuleSet(
            d,
            "update_apply_on_update",
            add(longConst(-7000), ScaleFeature.createScaled(
                FindDepthFeature.INSTANCE, 10.0)));
        bindRuleSet(d, "update_join", -4600);
        bindRuleSet(d, "update_apply", -4500);
        */

        //setUpStringNormalisation(d);

        //setupSplitting(d);

        /*
        bindRuleSet(d, "test_gen", inftyConst());
        bindRuleSet(d, "test_gen_empty_modality_hide", inftyConst());
        bindRuleSet(d, "test_gen_quan", inftyConst());
        bindRuleSet(d, "test_gen_quan_num", inftyConst());
         */

        /*
        bindRuleSet(
            d,
            "gamma",
            add(not(isInstantiated("t")),
                ifZero(allowQuantifierSplitting(), longConst(0),
                    longConst(50))));
        bindRuleSet(d, "gamma_destructive", inftyConst());

        bindRuleSet(d, "triggered",  add(not(isTriggerVariableInstantiated()), longConst(500)));

        bindRuleSet(
            d,
            "comprehension_split",
            add(applyTF(FocusFormulaProjection.INSTANCE,
                    ff.notContainsExecutable),
                ifZero(allowQuantifierSplitting(), longConst(2500),
                    longConst(5000))));
        */
        /*
        setupReplaceKnown(d);

        //setupApplyEq(d, numbers);

        bindRuleSet(
            d,
            "insert_eq_nonrigid",
            applyTF(FocusProjection.create(0),
                IsNonRigidTermFeature.INSTANCE));


        bindRuleSet(
            d,
            "order_terms",
            add(ifZero(
                    applyTF("commEqLeft", tf.intF),
                    add(applyTF("commEqRight", tf.monomial),
                        applyTF("commEqLeft", tf.polynomial),
                        monSmallerThan("commEqLeft", "commEqRight",
                            numbers)),
                    termSmallerThan("commEqLeft", "commEqRight")),
                longConst(-5000)));*/

        /*
        bindRuleSet(d, "simplify_literals",
            // ifZero ( ConstraintStrengthenFeatureUC.create(proof),
            // longConst ( 0 ),
            longConst(-8000));

        bindRuleSet(d, "simplify_instanceof_static",
            add(EqNonDuplicateAppFeature.INSTANCE, longConst(-500)));

        bindRuleSet(
            d,
            "comprehensions",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                longConst(-50)));

        bindRuleSet(
            d,
            "comprehensions_high_costs",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                longConst(10000)));

        bindRuleSet(
            d,
            "comprehensions_low_costs",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                longConst(-5000)));

        bindRuleSet(d, "evaluate_instanceof", longConst(-500));

        bindRuleSet(d, "instanceof_to_exists", TopLevelFindFeature.ANTEC);

        bindRuleSet(d, "try_apply_subst",
            add(EqNonDuplicateAppFeature.INSTANCE, longConst(-10000)));

         */

        final TermBuffer superFor = new TermBuffer();
        bindRuleSet(
            d,
            "split_if",
            add(sum(superFor,
                SuperTermGenerator.upwards(any(), proof.getServices()),
                applyTF(superFor, not(ff.program))), longConst(50)));

        final String[] exceptionsWithPenalty =
            new String[] {"java.lang.NullPointerException",
                "java.lang.ArrayIndexOutOfBoundsException",
                "java.lang.ArrayStoreException",
                "java.lang.ClassCastException"};

        bindRuleSet(
            d,
            "simplify_prog",
            ifZero(ThrownExceptionFeature.create(exceptionsWithPenalty,
                    proof.getServices()),
                longConst(500),
                ifZero(isBelow(add(ff.forF, not(ff.atom))),
                    longConst(200), longConst(-100))));

        bindRuleSet(d, "simplify_prog_subset", longConst(-4000));
        bindRuleSet(d, "modal_tautology", longConst(-10000));

        // features influenced by the strategy options

        boolean useLoopExpand =
            strategyProperties.getProperty(
                StrategyProperties.LOOP_OPTIONS_KEY).equals(
                StrategyProperties.LOOP_EXPAND);
        boolean useLoopInvTaclets =
            strategyProperties.getProperty(
                StrategyProperties.LOOP_OPTIONS_KEY).equals(
                StrategyProperties.LOOP_SCOPE_INV_TACLET);
        boolean useLoopScopeExpand =
            strategyProperties.getProperty(
                StrategyProperties.LOOP_OPTIONS_KEY).equals(
                StrategyProperties.LOOP_SCOPE_EXPAND);
        /*
         * boolean useBlockExpand = strategyProperties.getProperty(
         * StrategyProperties.BLOCK_OPTIONS_KEY).
         * equals(StrategyProperties.BLOCK_EXPAND);
         */
        boolean programsToRight = true; // XXX

        final String methProp =
            strategyProperties
                .getProperty(StrategyProperties.METHOD_OPTIONS_KEY);

        switch (methProp) {
        case StrategyProperties.METHOD_CONTRACT:
            /*
             * If method treatment by contracts is chosen, this does not mean
             * that method expansion is disabled. The original cost was 200 and
             * is now increased to 2000 in order to repress method expansion
             * stronger when method treatment by contracts is chosen.
             */
            bindRuleSet(d, "method_expand", longConst(2000));
            break;
        case StrategyProperties.METHOD_EXPAND:
            bindRuleSet(d, "method_expand", longConst(100));
            break;
        case StrategyProperties.METHOD_NONE:
            bindRuleSet(d, "method_expand", inftyConst());
            break;
        default:
            throw new RuntimeException("Unexpected strategy property "
                + methProp);
        }

        final String mpsProp =
            strategyProperties
                .getProperty(StrategyProperties.MPS_OPTIONS_KEY);

        switch (mpsProp) {
        case StrategyProperties.MPS_MERGE:
            /*
             * For this case, we use a special feature, since deleting merge
             * points should only be done after a merge rule application.
             */
            bindRuleSet(d, "merge_point", DeleteMergePointRuleFeature.INSTANCE);
            break;
        case StrategyProperties.MPS_SKIP:
            bindRuleSet(d, "merge_point", longConst(-5000));
            break;
        case StrategyProperties.MPS_NONE:
            bindRuleSet(d, "merge_point", inftyConst());
            break;
        default:
            throw new RuntimeException("Unexpected strategy property "
                + methProp);
        }


        final String queryAxProp =
            strategyProperties
                .getProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY);
        switch (queryAxProp) {
        case StrategyProperties.QUERYAXIOM_ON:
            bindRuleSet(d, "query_axiom", longConst(-3000));
            break;
        case StrategyProperties.QUERYAXIOM_OFF:
            bindRuleSet(d, "query_axiom", inftyConst());
            break;
        default:
            throw new RuntimeException("Unexpected strategy property "
                + queryAxProp);
        }

        /*
        if (classAxiomApplicationEnabled()) {
            bindRuleSet(d, "classAxiom", longConst(-250));
        } else {
            bindRuleSet(d, "classAxiom", inftyConst());
        }*/

        bindRuleSet(d, "loop_expand", useLoopExpand ? longConst(0)
            : inftyConst());
        bindRuleSet(d, "loop_scope_inv_taclet",
            useLoopInvTaclets ? longConst(0) : inftyConst());
        bindRuleSet(d, "loop_scope_expand",
            useLoopScopeExpand ? longConst(1000) : inftyConst());

        /*
         * bindRuleSet ( d, "block_expand", useBlockExpand ? longConst ( 0 ) :
         * inftyConst () );
         */

        // delete cast
        bindRuleSet(
            d,
            "cast_deletion",
            ifZero(implicitCastNecessary(instOf("castedTerm")),
                longConst(-5000), inftyConst()));

        bindRuleSet(d, "type_hierarchy_def", -6500);

        // partial inv axiom
        bindRuleSet(
            d,
            "partialInvAxiom",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                longConst(10000)));

        // inReachableState
        bindRuleSet(d, "inReachableStateImplication",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(100)));

        // limit observer (must have better priority than "classAxiom")
        bindRuleSet(
            d,
            "limitObserver",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(-200)));

        if (programsToRight) {
            bindRuleSet(
                d,
                "boxDiamondConv",
                SumFeature
                    .createSum(
                        new FindPrefixRestrictionFeature(
                            FindPrefixRestrictionFeature
                                .PositionModifier.ALLOW_UPDATE_AS_PARENT,
                            FindPrefixRestrictionFeature
                                .PrefixChecker.ANTEC_POLARITY),
                        longConst(-1000)));
        } else {
            bindRuleSet(d, "boxDiamondConv", inftyConst());
        }

        //bindRuleSet(d, "cut", not(isInstantiated("cutFormula")));

        //setupUserTaclets(d);

        //setupArithPrimaryCategories(d);
        //setupPolySimp(d, numbers);
        //setupInEqSimp(d, numbers);

        /*
        if (quantifierInstantiatedEnabled()) {
            setupFormulaNormalisation(d, numbers, locSetLDT);
        } else {
            bindRuleSet(d, "negationNormalForm", inftyConst());
            bindRuleSet(d, "moveQuantToLeft", inftyConst());
            bindRuleSet(d, "conjNormalForm", inftyConst());
            bindRuleSet(d, "apply_equations_andOr", inftyConst());
            bindRuleSet(d, "elimQuantifier", inftyConst());
            bindRuleSet(d, "distrQuantifier", inftyConst());
            bindRuleSet(d, "swapQuantifiers", inftyConst());
            bindRuleSet(d, "pullOutQuantifierAll", inftyConst());
            bindRuleSet(d, "pullOutQuantifierEx", inftyConst());
        }
         */

        return d;
    }

    private void setupFormulaNormalisation(RuleSetDispatchFeature d,
                                           IntegerLDT numbers, LocSetLDT locSetLDT) {

        bindRuleSet(
            d,
            "negationNormalForm",
            add(not(NotBelowBinderFeature.INSTANCE), longConst(-500),
                ScaleFeature.createScaled(FindDepthFeature.INSTANCE,
                    10.0)));

        bindRuleSet(
            d,
            "moveQuantToLeft",
            add(quantifiersMightSplit() ? longConst(0) : applyTF(
                FocusFormulaProjection.INSTANCE,
                ff.quantifiedPureLitConjDisj), longConst(-550)));

        bindRuleSet(
            d,
            "conjNormalForm",
            ifZero(add(
                    or(FocusInAntecFeature.INSTANCE,
                        NotBelowQuantifierFeature.INSTANCE),
                    NotInScopeOfModalityFeature.INSTANCE),
                add(longConst(-150), ScaleFeature.createScaled(
                    FindDepthFeature.INSTANCE, 20)), inftyConst()));

        bindRuleSet(d, "setEqualityBlastingRight", longConst(-100));

        bindRuleSet(
            d,
            "cnf_setComm",
            add(SetsSmallerThanFeature.create(instOf("commRight"),
                    instOf("commLeft"), locSetLDT),
                NotInScopeOfModalityFeature.INSTANCE, longConst(-800)));

        bindRuleSet(d, "elimQuantifier", -1000);
        bindRuleSet(d, "elimQuantifierWithCast", 50);

        final TermBuffer left = new TermBuffer();
        final TermBuffer right = new TermBuffer();
        bindRuleSet(
            d,
            "apply_equations_andOr",
            add(let(left,
                instOf("applyEqLeft"),
                let(right,
                    instOf("applyEqRight"),
                    ifZero(applyTF(left, tf.intF),
                        add(applyTF(left,
                                tf.nonNegOrNonCoeffMonomial),
                            applyTF(right, tf.polynomial),
                            MonomialsSmallerThanFeature
                                .create(right, left,
                                    numbers)),
                        TermSmallerThanFeature.create(right,
                            left)))), longConst(-150)));

        bindRuleSet(
            d,
            "distrQuantifier",
            add(or(applyTF(
                    FocusProjection.create(0),
                    add(ff.quantifiedClauseSet,
                        not(opSub(Quantifier.ALL, ff.orF)),
                        EliminableQuantifierTF.INSTANCE)), SumFeature
                    .createSum(
                        OnlyInScopeOfQuantifiersFeature.INSTANCE,
                        SplittableQuantifiedFormulaFeature.INSTANCE,
                        ifZero(FocusInAntecFeature.INSTANCE,
                            applyTF(FocusProjection.create(0),
                                sub(ff.andF)),
                            applyTF(FocusProjection.create(0),
                                sub(ff.orF))))),
                longConst(-300)));

        bindRuleSet(
            d,
            "swapQuantifiers",
            add(applyTF(
                    FocusProjection.create(0),
                    add(ff.quantifiedClauseSet,
                        EliminableQuantifierTF.INSTANCE,
                        sub(not(EliminableQuantifierTF.INSTANCE)))),
                longConst(-300)));

        // category "conjunctive normal form"

        bindRuleSet(d, "cnf_orComm", SumFeature.createSum(new Feature[] {
            applyTF("commRight", ff.clause),
            applyTFNonStrict("commResidue", ff.clauseSet),
            or(applyTF("commLeft", ff.andF),
                add(applyTF("commLeft", ff.literal),
                    literalsSmallerThan("commRight", "commLeft",
                        numbers))), longConst(-100) }));

        bindRuleSet(
            d,
            "cnf_orAssoc",
            SumFeature.createSum(new Feature[] {
                applyTF("assoc0", ff.clause),
                applyTF("assoc1", ff.clause),
                applyTF("assoc2", ff.literal), longConst(-80) }));

        bindRuleSet(d, "cnf_andComm", SumFeature.createSum(new Feature[] {
            applyTF("commLeft", ff.clause),
            applyTF("commRight", ff.clauseSet),
            applyTFNonStrict("commResidue", ff.clauseSet),
            // at least one of the subformulas has to be a literal;
            // otherwise,
            // sorting is not likely to have any big effect
            ifZero(add(applyTF("commLeft", not(ff.literal)),
                    applyTF("commRight", rec(ff.andF, not(ff.literal)))),
                longConst(100), longConst(-60)),
            clausesSmallerThan("commRight", "commLeft", numbers) }));

        bindRuleSet(
            d,
            "cnf_andAssoc",
            SumFeature.createSum(new Feature[] {
                applyTF("assoc0", ff.clauseSet),
                applyTF("assoc1", ff.clauseSet),
                applyTF("assoc2", ff.clause), longConst(-10) }));

        bindRuleSet(d, "cnf_dist", SumFeature.createSum(new Feature[] {
            applyTF("distRight0", ff.clauseSet),
            applyTF("distRight1", ff.clauseSet),
            ifZero(applyTF("distLeft", ff.clause), longConst(-15),
                applyTF("distLeft", ff.clauseSet)), longConst(-35) }));

        final TermBuffer superFor = new TermBuffer();
        final Feature onlyBelowQuanAndOr =
            sum(superFor,
                SuperTermGenerator.upwards(any(), getServices()),
                applyTF(superFor, or(ff.quantifiedFor, ff.andF, ff.orF)));

        final Feature belowUnskolemisableQuantifier =
            ifZero(FocusInAntecFeature.INSTANCE,
                not(sum(superFor, SuperTermGenerator.upwards(any(),
                        getServices()),
                    not(applyTF(superFor, op(Quantifier.ALL))))),
                not(sum(superFor, SuperTermGenerator.upwards(any(),
                        getServices()),
                    not(applyTF(superFor, op(Quantifier.EX))))));

        bindRuleSet(
            d,
            "cnf_expandIfThenElse",
            add(not(NotBelowQuantifierFeature.INSTANCE),
                onlyBelowQuanAndOr, belowUnskolemisableQuantifier));

        final Feature pullOutQuantifierAllowed =
            add(not(NotBelowQuantifierFeature.INSTANCE),
                onlyBelowQuanAndOr,
                applyTF(FocusProjection.create(0),
                    sub(ff.quantifiedClauseSet,
                        ff.quantifiedClauseSet)));

        bindRuleSet(d, "pullOutQuantifierUnifying", -20);

        bindRuleSet(
            d,
            "pullOutQuantifierAll",
            add(pullOutQuantifierAllowed,
                ifZero(FocusInAntecFeature.INSTANCE, longConst(-20),
                    longConst(-40))));

        bindRuleSet(
            d,
            "pullOutQuantifierEx",
            add(pullOutQuantifierAllowed,
                ifZero(FocusInAntecFeature.INSTANCE, longConst(-40),
                    longConst(-20))));
    }

    private Feature clausesSmallerThan(String smaller, String bigger,
                                       IntegerLDT numbers) {
        return ClausesSmallerThanFeature.create(instOf(smaller),
            instOf(bigger), numbers);
    }

    private void setupSelectSimplification(final RuleSetDispatchFeature d) {
        bindRuleSet(d, "pull_out_select",
            // pull out select only if it can be simplified
            // (the heap term may not be the base heap or an anon heap
            // function symbol)
            add(applyTF(
                    "h",
                    not(or(PrimitiveHeapTermFeature.create(heapLDT),
                        AnonHeapTermFeature.INSTANCE))),
                ifZero(applyTF(FocusFormulaProjection.INSTANCE,
                    ff.update), longConst(-4200), longConst(-1900)),
                NonDuplicateAppModPositionFeature.INSTANCE));
        bindRuleSet(d, "apply_select_eq",
            // replace non-simplified select by the skolem constant
            // of the corresponding pull out; at least one select
            // needs to be not simplified yet; additional restrictions
            // in isApproved()
            ifZero(applyTF(
                    "s",
                    not(rec(any(),
                        SimplifiedSelectTermFeature.create(heapLDT)))),
                // together with the costs of apply_equations the
                // resulting costs are about -5700
                longConst(-1700)));
        bindRuleSet(d, "simplify_select",
            // simplify_select term in pulled out equation (right hand
            // side has to be a skolem constant which has been
            // introduced by a select pull out; left hand side needs
            // to be a select term on a non-base- and
            // non-anon-heap)
            add(applyTF("sk", IsSelectSkolemConstantTermFeature.INSTANCE),
                applyTF(sub(FocusProjection.INSTANCE, 0),
                    not(SimplifiedSelectTermFeature.create(heapLDT))),
                longConst(-5600)));
        bindRuleSet(d,
            "apply_auxiliary_eq",
            // replace skolem constant by it's computed value
            add(applyTF("t1", IsSelectSkolemConstantTermFeature.INSTANCE),
                longConst(-5500)));
        bindRuleSet(
            d,
            "hide_auxiliary_eq",
            // hide auxiliary equation after the skolem constants have
            // been replaced by it's computed value
            add(applyTF("auxiliarySK",
                    IsSelectSkolemConstantTermFeature.INSTANCE),
                applyTF("result",
                    rec(any(),
                        add(SimplifiedSelectTermFeature
                                .create(heapLDT),
                            not(ff.ifThenElse)))),
                not(ContainsTermFeature.create(instOf("result"),
                    instOf("auxiliarySK"))), longConst(-5400)));
        bindRuleSet(
            d,
            "hide_auxiliary_eq_const",
            // hide auxiliary equation after the skolem constatns have
            // been replaced by it's computed value
            add(applyTF("auxiliarySK",
                    IsSelectSkolemConstantTermFeature.INSTANCE),
                longConst(-500)));
    }

    private void setUpStringNormalisation(RuleSetDispatchFeature d) {

        // translates an integer into its string representation
        bindRuleSet(d, "integerToString", -10000);

        // do not convert char to int when inside a string function
        // feature used to recognize if one is inside a string literal
        final SeqLDT seqLDT =
            getServices().getTypeConverter().getSeqLDT();
        final CharListLDT charListLDT =
            getServices().getTypeConverter().getCharListLDT();
        final BooleanLDT booleanLDT =
            getServices().getTypeConverter().getBooleanLDT();


        final TermFeature keepChar =
            or(op(seqLDT.getSeqSingleton()),
                or(op(charListLDT.getClIndexOfChar()),
                    or (op(charListLDT.getClReplace()),
                        op(charListLDT.getClLastIndexOfChar()))));

        //bindRuleSet(d, "charLiteral_to_intLiteral",
        //    ifZero(isBelow(keepChar), inftyConst(), longConst(-100)));

        // establish normalform

        // tf below only for test
        final TermFeature anyLiteral =
            or(tf.charLiteral,
                or(tf.literal, op(booleanLDT.getFalseConst()), op(booleanLDT.getTrueConst())));

        final TermFeature seqLiteral =
            rec(anyLiteral,
                or(op(seqLDT.getSeqConcat()),
                    or(op(seqLDT.getSeqSingleton()),
                        or(anyLiteral, inftyTermConst()))));

        Feature belowModOpPenality =
            ifZero(isBelow(ff.modalOperator), longConst(500));

        bindRuleSet(
            d,
            "defOpsSeqEquality",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                ifZero(add(applyTF("left", seqLiteral),
                        applyTF("right", seqLiteral)),
                    longConst(1000), inftyConst()),
                belowModOpPenality));

        bindRuleSet(
            d,
            "defOpsConcat",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                ifZero(or(applyTF("leftStr", not(seqLiteral)),
                        applyTF("rightStr", not(seqLiteral))),
                    longConst(1000)
                    // concat is often introduced for construction purposes,
                    // we do not want to use its definition right at the
                    // beginning
                ), belowModOpPenality));

        bindRuleSet(d, "stringsSimplify", longConst(-5000));

        final TermFeature charOrIntLiteral =
            or(tf.charLiteral, tf.literal,
                or(add(OperatorClassTF.create(SortDependingFunction.class), // XXX:
                    // was CastFunctionSymbol.class
                    sub(tf.literal)), inftyTermConst()));

        bindRuleSet(
            d,
            "defOpsReplaceInline",
            ifZero(add(applyTF("str", seqLiteral),
                applyTF("searchChar", charOrIntLiteral),
                applyTF("replChar", charOrIntLiteral)), longConst(-2500), inftyConst()));

        bindRuleSet(
            d,
            "defOpsReplace",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                ifZero(or(applyTF("str", not(seqLiteral)),
                        applyTF("searchChar", not(charOrIntLiteral)),
                        applyTF("replChar", not(charOrIntLiteral))),
                    longConst(500), inftyConst()),
                belowModOpPenality));

        bindRuleSet(d, "stringsReduceSubstring",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(100)));

        bindRuleSet(d, "defOpsStartsEndsWith", longConst(250));

        bindRuleSet(
            d,
            "stringsConcatNotBothLiterals",
            ifZero(MatchedIfFeature.INSTANCE,
                ifZero(add(applyTF(instOf("leftStr"), seqLiteral),
                        applyTF(instOf("rightStr"), seqLiteral)),
                    inftyConst()), inftyConst()));

        bindRuleSet(d, "stringsReduceConcat", longConst(100));

        bindRuleSet(
            d,
            "stringsReduceOrMoveOutsideConcat",
            ifZero(NonDuplicateAppModPositionFeature.INSTANCE,
                longConst(800), inftyConst()));

        bindRuleSet(
            d,
            "stringsMoveReplaceInside",
            ifZero(NonDuplicateAppModPositionFeature.INSTANCE,
                longConst(400), inftyConst()));


        bindRuleSet(d, "stringsExpandDefNormalOp", longConst(500));

        bindRuleSet(
            d,
            "stringsContainsDefInline",
            SumFeature.createSum(
                new Feature[] {EqNonDuplicateAppFeature.INSTANCE,
                    longConst(1000)}));
    }

    private void setupReplaceKnown(RuleSetDispatchFeature d) {
        final Feature commonF =
            add(ifZero(MatchedIfFeature.INSTANCE,
                    DiffFindAndIfFeature.INSTANCE),
                longConst(-5000),
                add(DiffFindAndReplacewithFeature.INSTANCE,
                    ScaleFeature.createScaled(
                        CountMaxDPathFeature.INSTANCE, 10.0)));

        bindRuleSet(d, "replace_known_left", commonF);
        bindRuleSet(
            d,
            "replace_known_right",
            add(commonF,
                ifZero(DirectlyBelowSymbolFeature
                        .create(Junctor.IMP, 1),
                    longConst(100),
                    ifZero(DirectlyBelowSymbolFeature
                        .create(Equality.EQV), longConst(100)))));
    }

    private void setupUserTaclets(RuleSetDispatchFeature d) {
        for (int i = 1; i <= StrategyProperties.USER_TACLETS_NUM; ++i) {
            final String userTacletsProbs =
                strategyProperties.getProperty(StrategyProperties
                    .userTacletsOptionsKey(i));
            if (StrategyProperties.USER_TACLETS_LOW.equals(userTacletsProbs)) {
                bindRuleSet(d, "userTaclets" + i, 10000);
            } else if (StrategyProperties.USER_TACLETS_HIGH
                .equals(userTacletsProbs)) {
                bindRuleSet(d, "userTaclets" + i, -50);
            } else {
                bindRuleSet(d, "userTaclets" + i, inftyConst());
            }
        }
    }

    private void setupSystemInvariantSimp(RuleSetDispatchFeature d) {
        bindRuleSet(
            d,
            "system_invariant",
            ifZero(MatchedIfFeature.INSTANCE,
                add(applyTF("negLit", tf.negLiteral),
                    applyTFNonStrict("nonNegLit", tf.nonNegLiteral))));
    }

    private void setupSplitting(RuleSetDispatchFeature d) {
        final TermBuffer subFor = new TermBuffer();
        final Feature noCutsAllowed =
            sum(subFor, AllowedCutPositionsGenerator.INSTANCE,
                not(applyTF(subFor, ff.cutAllowed)));
        bindRuleSet(d, "beta", SumFeature.createSum(noCutsAllowed,
            ifZero(PurePosDPathFeature.INSTANCE, longConst(-200)),
            ScaleFeature.createScaled(CountPosDPathFeature.INSTANCE, -3.0),
            ScaleFeature.createScaled(CountMaxDPathFeature.INSTANCE, 10.0),
            longConst(20)));
        TermBuffer superF = new TermBuffer();
        final ProjectionToTerm splitCondition = sub(FocusProjection.INSTANCE, 0);
        bindRuleSet(d,
            "split_cond",
            add(// do not split over formulas containing auxiliary variables
                applyTF(FocusProjection.INSTANCE,
                    rec(any(), not(IsSelectSkolemConstantTermFeature.INSTANCE))),
                // prefer splits when condition has quantifiers (less
                // likely to be simplified away)
                applyTF(splitCondition,
                    rec(ff.quantifiedFor,
                        ifZero(ff.quantifiedFor, longTermConst(-10)))),
                FindDepthFeature.INSTANCE, // prefer top level splits
                ScaleFeature.createAffine(countOccurrences(splitCondition), -10, 10),
                sum(superF, SuperTermGenerator.upwards(any(), getServices()),
                    applyTF(superF, not(ff.elemUpdate))),
                ifZero(applyTF(FocusProjection.INSTANCE,
                        ContainsExecutableCodeTermFeature.PROGRAMS),
                    longConst(-100), longConst(25))));
        ProjectionToTerm cutFormula = instOf("cutFormula");
        Feature countOccurrencesInSeq =
            ScaleFeature.createAffine(countOccurrences(cutFormula), -10, 10);
        /*
        bindRuleSet(
            d,
            "cut_direct",
            SumFeature
                .createSum(
                    new Feature[] {
                        not(TopLevelFindFeature.ANTEC_OR_SUCC_WITH_UPDATE),
                        AllowedCutPositionFeature.INSTANCE,
                        ifZero(NotBelowQuantifierFeature.INSTANCE,
                            add(applyTF(cutFormula,
                                    add(ff.cutAllowed,
                                        // do not cut over formulas containing
                                        // auxiliary variables
                                        rec(any(),
                                            not(IsSelectSkolemConstantTermFeature.INSTANCE)))),
                                // prefer cuts over "something = null"
                                ifZero(applyTF(FocusProjection.INSTANCE,
                                        opSub(tf.eq, any(), vf.nullTerm)),
                                    longConst(-5), longConst(0)),
                                // punish cuts over formulas containing anon heap functions
                                ifZero(applyTF(cutFormula,
                                        rec(any(), not(AnonHeapTermFeature.INSTANCE))),
                                    longConst(0), longConst(1000)),
                                countOccurrencesInSeq, // standard costs
                                longConst(100)),
                            SumFeature // check for cuts below quantifiers
                                .createSum(
                                    new Feature[] {
                                        applyTF(cutFormula, ff.cutAllowedBelowQuantifier),
                                        applyTF(FocusFormulaProjection.INSTANCE,
                                            ff.quantifiedClauseSet),
                                        ifZero(allowQuantifierSplitting(),
                                            longConst(0), longConst(100))}))}));

         */
    }

    private Feature isBelow(TermFeature t) {
        final TermBuffer superTerm = new TermBuffer();
        return not(sum(superTerm,
            SuperTermGenerator.upwards(any(), getServices()),
            not(applyTF(superTerm, t))));
    }

    private boolean classAxiomApplicationEnabled() {
        String classAxiomSetting =
            strategyProperties
                .getProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY);
        return !StrategyProperties.CLASS_AXIOM_OFF.equals(classAxiomSetting);
    }

    private Feature allowQuantifierSplitting() {
        if (StrategyProperties.QUANTIFIERS_INSTANTIATE
            .equals(strategyProperties
                .getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY))) {
            return longConst(0);
        }
        if (StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS
            .equals(strategyProperties
                .getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY))) {
            return sequentContainsNoPrograms();
        }
        return inftyConst();
    }

    private boolean quantifierInstantiatedEnabled() {
        return !StrategyProperties.QUANTIFIERS_NONE.equals(strategyProperties
            .getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY));
    }

    private boolean quantifiersMightSplit() {
        return StrategyProperties.QUANTIFIERS_INSTANTIATE
            .equals(strategyProperties
                .getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY))
            || StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS
            .equals(strategyProperties
                .getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY));
    }
}
