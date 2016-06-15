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

package de.uka.ilkd.key.symbolic_execution.profile;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.label.SingletonLabelFactory;
import de.uka.ilkd.key.logic.label.TermLabelManager.TermLabelConfiguration;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.label.TermLabelPolicy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.symbolic_execution.strategy.SimplifyTermStrategy;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * An extended {@link JavaProfile} used in side proofs to simplify a {@link JavaDLTerm}.
 * @author Martin Hentschel
 */
public class SimplifyTermProfile extends JavaProfile {
   /**
    * The {@link Name} of this {@link Profile}.
    */
   public static final String NAME = "Java Profile for JavaDLTerm Simplification";
   
   /**
    * The used {@link StrategyFactory} of the {@link SymbolicExecutionStrategy}.
    */
   private final static StrategyFactory SIDE_PROOF_FACTORY = new SimplifyTermStrategy.Factory();
   
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
   public static SimplifyTermProfile defaultInstance;

   /**
    * Constructor.
    */
   public SimplifyTermProfile() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ImmutableList<TermLabelConfiguration> computeTermLabelConfiguration() {
      ImmutableList<TermLabelConfiguration> result = super.computeTermLabelConfiguration();
      ImmutableList<TermLabelPolicy> symExcPolicies = ImmutableSLList.<TermLabelPolicy>nil().prepend(new TermLabelPolicy() {
         @Override
         public TermLabel keepLabel(TermLabelState state, Services services,
               PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> applicationPosInOccurrence,
               JavaDLTerm applicationTerm, Rule rule, Goal goal, Object hint,
               JavaDLTerm tacletTerm, Operator newTermOp,
               ImmutableArray<JavaDLTerm> newTermSubs,
               ImmutableArray<QuantifiableVariable> newTermBoundVars,
               JavaBlock newTermJavaBlock, ImmutableArray<TermLabel> newTermOriginalLabels, TermLabel label) {
            return label;
         }
       });
       result = result.prepend(new TermLabelConfiguration(SymbolicExecutionUtil.RESULT_LABEL_NAME,
                                                          new SingletonLabelFactory<TermLabel>(SymbolicExecutionUtil.RESULT_LABEL),
                                                          null,
                                                          symExcPolicies,
                                                          null,
                                                          null,
                                                          null,
                                                          null,
                                                          null));       
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected ImmutableSet<StrategyFactory> getStrategyFactories() {
      return DefaultImmutableSet.<StrategyFactory>nil().add(SIDE_PROOF_FACTORY);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public StrategyFactory getDefaultStrategyFactory() {
      return SIDE_PROOF_FACTORY;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String name() {
      return NAME;
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
    * @return The default instance for usage in the {@link Thread} of the user interface.
    */
   public static synchronized SimplifyTermProfile getDefaultInstance() {
       if (defaultInstance == null) {
           defaultInstance = new SimplifyTermProfile();
       }
      return defaultInstance;
   }
}