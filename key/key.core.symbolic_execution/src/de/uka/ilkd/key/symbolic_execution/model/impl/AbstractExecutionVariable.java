package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Provides a basic implementation of {@link IExecutionVariable}s.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionVariable extends AbstractExecutionElement implements IExecutionVariable {
   /**
    * The represented {@link IProgramVariable} which value is shown.
    */
   private final IProgramVariable programVariable;
   
   /**
    * The parent {@link ExecutionValue} or {@code null} if not available.
    */
   private final IExecutionValue parentValue;
   
   /**
    * The index in the parent array.
    */
   private final JavaDLTerm arrayIndex;
   
   /**
    * An optional additional condition to consider.
    */
   private final JavaDLTerm additionalCondition;
   
   /**
    * The {@link PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>} of the modality of interest.
    */
   private final PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> modalityPIO;

   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param programVariable The represented {@link IProgramVariable} which value is shown.
    * @param parentValue The parent {@link IExecutionValue} or {@code null} if not available.
    * @param arrayIndex The index in the parent array.
    * @param additionalCondition An optional additional condition to consider.
    * @param modalityPIO The {@link PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>} of the modality of interest.
    */
   public AbstractExecutionVariable(ITreeSettings settings, 
                                    Node proofNode, 
                                    IProgramVariable programVariable, 
                                    IExecutionValue parentValue, 
                                    JavaDLTerm arrayIndex, 
                                    JavaDLTerm additionalCondition,
                                    PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> modalityPIO) {
      super(settings, proofNode);
      this.programVariable = programVariable;
      this.parentValue = parentValue;
      this.arrayIndex = arrayIndex;
      this.additionalCondition = additionalCondition;
      this.modalityPIO = modalityPIO;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public JavaDLTerm getAdditionalCondition() {
      return additionalCondition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      IProgramVariable pv = getProgramVariable();
      if (pv != null) {
         return SymbolicExecutionUtil.getDisplayString(pv);
      }
      else {
         return "[" + getArrayIndexString() + "]";
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProgramVariable getProgramVariable() {
      return programVariable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public JavaDLTerm getArrayIndex() {
      return arrayIndex;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getArrayIndexString() {
      return arrayIndex != null ? formatTerm(arrayIndex, getServices()) : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isArrayIndex() {
      return getArrayIndex() != null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Variable";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionValue getParentValue() {
      return parentValue;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> getModalityPIO() {
      return modalityPIO;
   }
}
