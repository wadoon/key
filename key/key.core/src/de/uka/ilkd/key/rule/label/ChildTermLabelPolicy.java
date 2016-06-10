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

import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.JavaDLTermServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;

/**
 * <p>
 * A {@link ChildTermLabelPolicy} is used by
 * {@link TermLabelManager#instantiateLabels(Services, PosInOccurrence, JavaDLTerm, JavaDLTerm, Rule, Goal, Object, JavaDLTerm, Operator, ImmutableArray, ImmutableArray, JavaBlock)}
 * to decide for each {@link TermLabel} on a child or grandchild of the application {@link JavaDLTerm} if it
 * should be re-added to the new {@link JavaDLTerm} or not.
 * </p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained
 * during prove read the documentation of interface {@link TermLabel}.
 * </p>
 * @author Martin Hentschel
 * @see TermLabel
 * @see TermLabelManager
 */
public interface ChildTermLabelPolicy extends RuleSpecificTask {
   /**
    * Decides if the currently active {@link Rule} application is supported or not.
    * If it is not supported no iteration over children will be executed.
    * Only if it returns {@code true} {@link #addLabel(Services, PosInOccurrence, JavaDLTerm, Rule, Goal, Object, JavaDLTerm, Operator, ImmutableArray, ImmutableArray, JavaBlock, JavaDLTerm, TermLabel)}
    * will be called if a child {@link JavaDLTerm} contains a managed label.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link JavaDLTerm} that is rewritten.
    * @param applicationTerm The {@link JavaDLTerm} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied.
    * @param goal The optional {@link Goal} on which the {@link JavaDLTerm} to create will be used.
    * @param hint An optional hint passed from the active rule to describe the term which should be created.
    * @param tacletTerm The optional {@link JavaDLTerm} in the taclet which is responsible to instantiate the new {@link JavaDLTerm} for the new proof node or {@code null} in case of built in rules.
    * @param newTermOp The new {@link Operator} of the {@link JavaDLTerm} to create.
    * @param newTermSubs The optional children of the {@link JavaDLTerm} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link JavaDLTerm} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link JavaDLTerm} to create.
    * @param label The {@link TermLabel} to decide if it should be kept or dropped.
    * @return {@code true} keep {@link TermLabel} and add it to the new {@link JavaDLTerm}. {@code false} drop {@link TermLabel} and do not need it to the new {@link JavaDLTerm}.
    */
   public boolean isRuleApplicationSupported(JavaDLTermServices services,
                                             PosInOccurrence applicationPosInOccurrence,
                                             JavaDLTerm applicationTerm,
                                             Rule rule,
                                             Goal goal,
                                             Object hint,
                                             JavaDLTerm tacletTerm,
                                             Operator newTermOp,
                                             ImmutableArray<JavaDLTerm> newTermSubs,
                                             ImmutableArray<QuantifiableVariable> newTermBoundVars,
                                             JavaBlock newTermJavaBlock);

   /**
    * <p>
    * Decides to add or not to add the given {@link TermLabel} on a child or
    * grandchild of the application {@link JavaDLTerm} to the new {@link JavaDLTerm} which will be created.
    * </p>
    * <p>
    * If the child {@link JavaDLTerm} is still a child of the new {@link JavaDLTerm} the label
    * will still exist independent from the result of this method on the child.
    * To remove it from the child a refacotring has to be used instead.
    * </p>
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link JavaDLTerm} that is rewritten.
    * @param applicationTerm The {@link JavaDLTerm} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied.
    * @param goal The optional {@link Goal} on which the {@link JavaDLTerm} to create will be used.
    * @param hint An optional hint passed from the active rule to describe the term which should be created.
    * @param tacletTerm The optional {@link JavaDLTerm} in the taclet which is responsible to instantiate the new {@link JavaDLTerm} for the new proof node or {@code null} in case of built in rules.
    * @param newTermOp The new {@link Operator} of the {@link JavaDLTerm} to create.
    * @param newTermSubs The optional children of the {@link JavaDLTerm} to create.
    * @param newTermBoundVars The optional {@link QuantifiableVariable}s of the {@link JavaDLTerm} to create.
    * @param newTermJavaBlock The optional {@link JavaBlock} of the {@link JavaDLTerm} to create.
    * @param childTerm The {@link JavaDLTerm} which is a child or grandchild of the application {@link JavaDLTerm} that provides the {@link TermLabel}.
    * @param label The {@link TermLabel} to decide if it should be kept or dropped.
    * @return {@code true} add {@link TermLabel} to new {@link JavaDLTerm}. {@code false} do not add {@link TermLabel} to new {@link JavaDLTerm}.
    */
   public boolean addLabel(JavaDLTermServices services,
                           PosInOccurrence applicationPosInOccurrence,
                           JavaDLTerm applicationTerm,
                           Rule rule,
                           Goal goal,
                           Object hint,
                           JavaDLTerm tacletTerm,
                           Operator newTermOp,
                           ImmutableArray<JavaDLTerm> newTermSubs,
                           ImmutableArray<QuantifiableVariable> newTermBoundVars,
                           JavaBlock newTermJavaBlock,
                           JavaDLTerm childTerm,
                           TermLabel label);
}