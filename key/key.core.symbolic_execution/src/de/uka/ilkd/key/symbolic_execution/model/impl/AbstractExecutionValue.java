package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.key_project.common.core.logic.calculus.PosInOccurrence;
import org.key_project.common.core.logic.calculus.SequentFormula;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Provides a basic implementation of {@link IExecutionValue}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionValue extends AbstractExecutionElement implements IExecutionValue {
   /**
    * The parent {@link IExecutionVariable} which provides this {@link IExecutionValue}.
    */
   private final IExecutionVariable variable;

   /**
    * The condition under which the variable has this value.
    */
   private final JavaDLTerm condition;
   
   /**
    * The {@link IExecutionConstraint}s.
    */
   private IExecutionConstraint[] constraints;
   
   /**
    * The value.
    */
   private final JavaDLTerm value;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    * @param variable The parent {@link IExecutionVariable} which contains this value.
    * @param condition The condition.
    * @param value The value.
    */
   public AbstractExecutionValue(ITreeSettings settings, 
                                 Node proofNode, 
                                 IExecutionVariable variable, 
                                 JavaDLTerm condition,
                                 JavaDLTerm value) {
      super(settings, proofNode);
      this.variable = variable;
      this.condition = condition;
      this.value = value;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionConstraint[] getConstraints() throws ProofInputException {
      synchronized (this) {
         if (constraints == null) {
            constraints = lazyComputeConstraints();
         }
         return constraints;
      }
   }
   
   /**
    * Computes the related constraints lazily when {@link #getConstraints()} is called the first time.
    * @return The related {@link IExecutionConstraint}s.
    * @throws ProofInputException Occurred Exception
    */
   protected IExecutionConstraint[] lazyComputeConstraints() throws ProofInputException {
      if (!isDisposed() && !isValueUnknown()) {
         List<IExecutionConstraint> constraints = new LinkedList<IExecutionConstraint>();
         IExecutionConstraint[] allConstraints = getNodeConstraints();
         Set<JavaDLTerm> relevantTerms = collectRelevantTerms(getServices(), getValue());
         for (IExecutionConstraint constraint : allConstraints) {
            if (containsTerm(constraint.getTerm(), relevantTerms)) {
               constraints.add(constraint);
            }
         }
         return constraints.toArray(new IExecutionConstraint[constraints.size()]);
      }
      else {
         return new IExecutionConstraint[0];
      }
   }
   
   /**
    * Returns all available {@link IExecutionConstraint}s of the {@link IExecutionNode} on which this {@link IExecutionValue} is part of.
    * @return All available {@link IExecutionConstraint}s.
    */
   protected abstract IExecutionConstraint[] getNodeConstraints();
   
   /**
    * Collects all {@link JavaDLTerm}s contained in relevant constraints.
    * @param services The {@link Services} to use.
    * @param term The initial {@link JavaDLTerm}.
    * @return The relevant {@link JavaDLTerm}s.
    */
   protected Set<JavaDLTerm> collectRelevantTerms(Services services, JavaDLTerm term) {
      final Set<JavaDLTerm> terms = new HashSet<JavaDLTerm>();
      fillRelevantTerms(services, term, terms);
      return terms;
   }
   
   /**
    * Utility method used by {@link #collectRelevantTerms(Services, JavaDLTerm)}.
    * @param services The {@link Services} to use.
    * @param term The initial {@link JavaDLTerm}.
    * @param toFill The {@link Set} of relevant {@link JavaDLTerm}s to fill.
    */
   protected void fillRelevantTerms(Services services, JavaDLTerm term, Set<JavaDLTerm> toFill) {
      if (term != null) {
         if (term.op() instanceof ProgramVariable ||
             SymbolicExecutionUtil.isSelect(services, term)) {
            toFill.add(term);
         }
         else {
            for (int i = 0; i < term.arity(); i++) {
               fillRelevantTerms(services, term.sub(i), toFill);
            }
         }
      }
   }

   /**
    * Checks if the given {@link JavaDLTerm} contains at least one of the given once.
    * @param term The {@link JavaDLTerm} to search in.
    * @param toSearch The {@link JavaDLTerm}s to search.
    * @return {@code true} at least one {@link JavaDLTerm} is contained, {@code false} none of the {@link JavaDLTerm}s is contained.
    */
   protected boolean containsTerm(JavaDLTerm term, Set<JavaDLTerm> toSearch) {
      if (toSearch.contains(term)) {
         return true;
      }
      else {
         boolean contained = false;
         int i = 0;
         while (!contained && i < term.arity()) {
            contained = containsTerm(term.sub(i), toSearch);
            i++;
         }
         return contained;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionVariable getVariable() {
      return variable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> getModalityPIO() {
      return getVariable().getModalityPIO();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() throws ProofInputException {
      String conditionString = getConditionString();
      if (conditionString != null) {
         return getVariable().getName() + " {" + getConditionString() + "}";
      }
      else {
         return getVariable().getName();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Value";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public JavaDLTerm getCondition() throws ProofInputException {
      return condition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public JavaDLTerm getValue() throws ProofInputException {
      return value;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isValueAnObject() throws ProofInputException {
      if (isValueUnknown()) {
         return false;
      }
      else {
         JavaDLTerm value = getValue();
         return SymbolicExecutionUtil.hasReferenceSort(getServices(), value);
      }
   }
}
