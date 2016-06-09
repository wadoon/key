package de.uka.ilkd.key.symbolic_execution.po;

import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.POExtension;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.symbolic_execution.TruthValueTracingUtil;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;

/**
 * Implementation of {@link POExtension} to support truth value evaluation.
 * @author Martin Hentschel
 */
public class TruthValuePOExtension implements POExtension {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isPOSupported(ProofOblInput po) {
      return po instanceof AbstractOperationPO;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public JavaDLTerm modifyPostTerm(InitConfig proofConfig, Services services, JavaDLTerm postTerm) {
      if (SymbolicExecutionJavaProfile.isTruthValueEvaluationEnabled(proofConfig)) {
         return labelPostTerm(services, postTerm);
      }
      else {
         return postTerm;
      }
   }
   
   /**
    * Labels all predicates in the given {@link JavaDLTerm} and its children with
    * a {@link FormulaTermLabel}.
    * @param services The {@link Services} to use.
    * @param term The {@link JavaDLTerm} to label.
    * @return The labeled {@link JavaDLTerm}.
    */
   protected JavaDLTerm labelPostTerm(Services services, JavaDLTerm term) {
      if (term != null) {
         final TermFactory tf = services.getTermFactory();
         // Label children of operator
         if (TruthValueTracingUtil.isLogicOperator(term)) {
            JavaDLTerm[] newSubs = new JavaDLTerm[term.arity()];
            boolean subsChanged = false;
            for (int i = 0; i < newSubs.length; i++) {
               JavaDLTerm oldTerm = term.sub(i);
               newSubs[i] = labelPostTerm(services, oldTerm);
               if (oldTerm != newSubs[i]) {
                  subsChanged = true;
               }
            }
            term = subsChanged ?
                   tf.createTerm(term.op(), new ImmutableArray<JavaDLTerm>(newSubs), term.boundVars(), term.modalContent(), term.getLabels()) :
                   term;
         }
         ImmutableArray<TermLabel> oldLabels = term.getLabels();
         TermLabel[] newLabels = oldLabels.toArray(new TermLabel[oldLabels.size() + 1]);
         int labelID = services.getCounter(FormulaTermLabel.PROOF_COUNTER_NAME).getCountPlusPlus();
         int labelSubID = FormulaTermLabel.newLabelSubID(services, labelID);
         newLabels[oldLabels.size()] = new FormulaTermLabel(labelID, labelSubID);
         return tf.createTerm(term.op(), term.subs(), term.boundVars(), term.modalContent(), new ImmutableArray<TermLabel>(newLabels));
      }
      else {
         return null;
      }
   }
}
