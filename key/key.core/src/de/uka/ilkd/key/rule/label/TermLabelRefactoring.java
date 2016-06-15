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

package de.uka.ilkd.key.rule.label;

import java.util.List;

import org.key_project.common.core.logic.GenericTermBuilder;
import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.label.TermLabel;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;

/**
 * <p>
 * A {@link TermLabelRefactoring} is used by
 * {@link TermLabelManager#refactorGoal(Services, PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>, JavaDLTerm, Rule, Goal, JavaDLTerm)}
 * to refactor the labels of each visited {@link JavaDLTerm}.
 * </p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained
 * during prove read the documentation of interface {@link TermLabel}.
 * </p>
 * @author Martin Hentschel
 * @see TermLabel
 * @see TermLabelManager
 */
public interface TermLabelRefactoring extends RuleSpecificTask {
   /**
    * Defines if a refactoring is required and if so in which {@link RefactoringScope}.
    * @param state The {@link TermLabelState} of the current rule application.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>} in the previous {@link Sequent} which defines the {@link JavaDLTerm} that is rewritten.
    * @param applicationTerm The {@link JavaDLTerm} defined by the {@link PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied.
    * @param goal The optional {@link Goal} on which the {@link JavaDLTerm} to create will be used.
    * @param hint An optional hint passed from the active rule to describe the term which should be created.
    * @param tacletTerm The optional taclet {@link JavaDLTerm}.
    * @return The required {@link RefactoringScope}.
    */
   public RefactoringScope defineRefactoringScope(TermLabelState state,
                                                  Services services,
                                                  PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> applicationPosInOccurrence,
                                                  JavaDLTerm applicationTerm,
                                                  Rule rule,
                                                  Goal goal,
                                                  Object hint,
                                                  JavaDLTerm tacletTerm);

   /**
    * This method is used to refactor the labels of the given {@link JavaDLTerm}.
    * @param state The {@link TermLabelState} of the current rule application.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>} in the previous {@link Sequent} which defines the {@link JavaDLTerm} that is rewritten.
    * @param applicationTerm The {@link JavaDLTerm} defined by the {@link PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied.
    * @param goal The optional {@link Goal} on which the {@link JavaDLTerm} to create will be used.
    * @param hint An optional hint passed from the active rule to describe the term which should be created.
    * @param tacletTerm The optional taclet {@link JavaDLTerm}.
    * @param term The {@link JavaDLTerm} which is now refactored.
    * @param labels The new labels the {@link JavaDLTerm} will have after the refactoring.
    */
   public void refactoreLabels(TermLabelState state,
                               Services services,
                               PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> applicationPosInOccurrence,
                               JavaDLTerm applicationTerm,
                               Rule rule,
                               Goal goal,
                               Object hint,
                               JavaDLTerm tacletTerm,
                               JavaDLTerm term,
                               List<TermLabel> labels);

   /**
    * Possible refactoring scopes.
    * @author Martin Hentschel
    */
   public static enum RefactoringScope {
      /**
       * No refactoring required.
       */
      NONE,

      /**
       * Refactor the child below the updates computed via
       * {@link GenericTermBuilder#goBelowUpdates(JavaDLTerm)}.
       */
      APPLICATION_BELOW_UPDATES,

      /**
       * Refactor direct children of the application term.
       */
      APPLICATION_DIRECT_CHILDREN,

      /**
       * Refactor children and grandchildren of the application term.
       */
      APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE,

      /**
       * Refactor the {@link SequentFormula} on which the rule is applied.
       */
      APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE_AND_PARENTS,
      
      /**
       * Refactor the whole sequent.
       */
      SEQUENT
   }
}