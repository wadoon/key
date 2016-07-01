package de.uka.ilkd.key.symbolic_execution.model.impl;

import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.calculus.SequentFormula;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

/**
 * The default implementation of {@link IExecutionConstraint}.
 * @author Martin Hentschel
 */
public class ExecutionConstraint extends AbstractExecutionElement implements IExecutionConstraint {
   /**
    * The {@link Term} representing the constraint.
    */
   private final Term term;
   
   /**
    * The {@link PosInOccurrence<Term>} of the modality of interest.
    */
   private final PosInOccurrence<Term> modalityPIO;

   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param term The {@link Term} representing the constraint.
    */
   public ExecutionConstraint(ITreeSettings settings, Node proofNode, PosInOccurrence<Term> modalityPIO, Term term) {
      super(settings, proofNode);
      assert term != null;
      assert modalityPIO != null;
      this.term = term;
      this.modalityPIO = modalityPIO;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      return formatTerm(term, getServices());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Constraint";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getTerm() {
      return term;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PosInOccurrence<Term> getModalityPIO() {
      return modalityPIO;
   }
}
