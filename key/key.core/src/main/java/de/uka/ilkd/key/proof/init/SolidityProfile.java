// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.init;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabelFactory;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.SingletonLabelFactory;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager.TermLabelConfiguration;
import de.uka.ilkd.key.proof.mgt.ComplexRuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.prover.impl.DepthFirstGoalChooserBuilder;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.label.OriginTermLabelPolicy;
import de.uka.ilkd.key.rule.label.OriginTermLabelRefactoring;
import de.uka.ilkd.key.rule.label.TermLabelPolicy;
import de.uka.ilkd.key.rule.label.TermLabelRefactoring;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyFactory;

/**
 * This profile sets up KeY for verification of JavaCard programs.
 *
 */
public class SolidityProfile extends AbstractProfile {
    public static final String NAME = "Solidity Profile";

    /**
     * <p>
     * The default instance of this class.
     * </p>
     * <p>
     * It is typically used in the {@link Thread} of the user interface.
     * Other instances of this class are typically only required to
     * use them in different {@link Thread}s (not the UI {@link Thread}).
     * </p>
     */
    public static SolidityProfile defaultInstance;
    public static SolidityProfile defaultInstancePermissions;

    public static final StrategyFactory DEFAULT =
        new JavaCardDLStrategyFactory();

    private OneStepSimplifier oneStepSimpilifier;

    protected SolidityProfile(String standardRules) {
        super(standardRules);
        setSelectedGoalChooserBuilder(DepthFirstGoalChooserBuilder.NAME);
    }

    public SolidityProfile() {
        this("standardRules-solidity.key");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected ImmutableList<TermLabelConfiguration> computeTermLabelConfiguration() {
        ImmutableList<TermLabelPolicy> originTermLabelPolicyList =
                ImmutableSLList.<TermLabelPolicy>nil().append(new OriginTermLabelPolicy());
        ImmutableList<TermLabelRefactoring> originTermLabelRefactorings =
                ImmutableSLList.<TermLabelRefactoring>nil().append(
                        new OriginTermLabelRefactoring());

        ImmutableList<TermLabelConfiguration> result = ImmutableSLList.nil();
        result = result.prepend(
            new TermLabelConfiguration(
                    ParameterlessTermLabel.ANON_HEAP_LABEL_NAME,
                    new SingletonLabelFactory<TermLabel>(
                            ParameterlessTermLabel.ANON_HEAP_LABEL)
            ));
        result = result.prepend(
            new TermLabelConfiguration(
                    ParameterlessTermLabel.SELECT_SKOLEM_LABEL_NAME,
                    new SingletonLabelFactory<TermLabel>(
                            ParameterlessTermLabel.SELECT_SKOLEM_LABEL)
            ));
        result = result.prepend(
            new TermLabelConfiguration(
                    ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL_NAME,
                    new SingletonLabelFactory<TermLabel>(
                            ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)
            ));
        result = result.prepend(
            new TermLabelConfiguration(
                    ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL_NAME,
                    new SingletonLabelFactory<TermLabel>(
                            ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL)
            ));
        result = result.prepend(
            new TermLabelConfiguration(
                    ParameterlessTermLabel.UNDEFINED_VALUE_LABEL_NAME,
                    new SingletonLabelFactory<TermLabel>(
                            ParameterlessTermLabel.UNDEFINED_VALUE_LABEL)
            ));
        result = result.prepend(
            new TermLabelConfiguration(
                    ParameterlessTermLabel.SELF_COMPOSITION_LABEL_NAME,
                    new SingletonLabelFactory<TermLabel>(
                            ParameterlessTermLabel.SELF_COMPOSITION_LABEL)
            ));
        result = result.prepend(
                new TermLabelConfiguration(
                        ParameterlessTermLabel.POST_CONDITION_LABEL_NAME,
                        new SingletonLabelFactory<TermLabel>(
                                ParameterlessTermLabel.POST_CONDITION_LABEL)
                ));
        result = result.prepend(
                new TermLabelConfiguration(
                        OriginTermLabel.NAME,
                        new OriginTermLabelFactory(),
                        originTermLabelPolicyList,
                        null,
                        null,
                        null,
                        null,
                        originTermLabelRefactorings,
                        null
                ));
        return result;
    }

    @Override
    protected ImmutableSet<StrategyFactory> getStrategyFactories() {
        ImmutableSet<StrategyFactory> set = super.getStrategyFactories();
        set = set.add(DEFAULT);
        return set;
    }


    @Override
    protected ImmutableList<BuiltInRule> initBuiltInRules() {
        ImmutableList<BuiltInRule> builtInRules = super.initBuiltInRules();

        builtInRules = builtInRules.prepend(getOneStepSimpilifier());

        return builtInRules;
    }

    /**
     * <p>
     * Returns the {@link OneStepSimplifier} instance which should be used
     * in this {@link SolidityProfile}. It is added to the build in rules via
     * {@link #initBuiltInRules()}.
     * </p>
     * <p>
     * Sub profiles may exchange the {@link OneStepSimplifier} instance,
     * for instance for site proofs used in the symbolic execution tree extraction.
     * </p>
     * @return The {@link OneStepSimplifier} instance to use.
     */
    public OneStepSimplifier getOneStepSimpilifier() {
        synchronized (this) {
            if (oneStepSimpilifier == null) {
                oneStepSimpilifier = new OneStepSimplifier();
            }
            return oneStepSimpilifier;
        }
    }

    /**
     * determines the justification of rule <code>r</code>. For a method contract rule it
     * returns a new instance of a {@link ComplexRuleJustification} otherwise the rule
     * justification determined by the super class is returned
     *
     * @param r the rule described above
     * @return justification for the given rule
     */
    @Override
    public RuleJustification getJustification(Rule r) {
        return super.getJustification(r);
    }


    /**
     * the name of the profile
     * @return the name
     */
    @Override
    public String name() {
        return NAME;
    }

    /**
     * the default strategy factory to be used
     * @return the default strategy factory
     */
    @Override
    public StrategyFactory getDefaultStrategyFactory() {
        return DEFAULT;
    }

    /**
     * <p>
     * Returns the default instance of this class.
     * </p>
     * <p>
     * It is typically used in the {@link Thread} of the user interface.
     * Other instances of this class are typically only required to
     * use them in different {@link Thread}s (not the UI {@link Thread}).
     * </p>
     * @param perms boolean to decide whether we use permissions
     * @return The default instance for usage in the {@link Thread} of the user interface.
     */
    public static synchronized SolidityProfile getDefaultInstance(boolean perms) {
    	if (defaultInstance == null) {
    		defaultInstance = new SolidityProfile();
    	}
    	return defaultInstance;
    }

    public static synchronized SolidityProfile getDefaultInstance() {
        return getDefaultInstance(false);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isSpecificationInvolvedInRuleApp(RuleApp app) {
        return false;
    }
}