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

package de.uka.ilkd.key.symbolic_execution.rule;

import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Namespace;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.Pair;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm<JavaDLTerm>;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionSideProofUtil;
import de.uka.ilkd.key.util.Triple;

/**
 * Provides the basic functionality of {@link BuiltInRule} which
 * computes something in a side proof.
 * @author Martin Hentschel
 */
public abstract class AbstractSideProofRule implements BuiltInRule {
   /**
    * <p>
    * Creates a constant which is used in the original {@link Proof} to
    * store the computed result in form of {@code QueryResult = ...}
    * </p>
    * <p>
    * The used name is registered in the {@link Namespace} of the {@link Services}.
    * </p>
    * @param services The {@link Services} to use-
    * @param sort The {@link Sort} to use.
    * @return The created constant.
    */
   protected Function createResultConstant(Services services, Sort sort) {
      String functionName = services.getTermBuilder().newName("QueryResult");
      Function function = new Function(new Name(functionName), sort);
      services.getNamespaces().functions().addSafely(function);
      return function;
   }
   
   /**
    * Creates the result {@link Function} used in a predicate to compute the result in the side proof.
    * @param services The {@link Services} to use.
    * @param sort The {@link Sort} to use.
    * @return The created result {@link Function}.
    */
   protected Function createResultFunction(Services services, Sort sort) {
      return new Function(new Name(services.getTermBuilder().newName("ResultPredicate")), Sort.FORMULA, sort);
   }
   
   /**
    * <p>
    * Starts the side proof and extracts the result {@link JavaDLTerm} and conditions.
    * </p>
    * <p>
    * New used names are automatically added to the {@link Namespace} of the {@link Services}.
    * </p>
    * @param services The {@link Services} to use.
    * @param goal The {@link Goal} on which this {@link BuiltInRule} should be applied on.
    * @param sideProofEnvironment The given {@link ProofEnvironment} of the side proof.
    * @param sequentToProve The {@link Sequent} to prove in a side proof.
    * @param newPredicate The {@link Function} which is used to compute the result.
    * @return The found result {@link JavaDLTerm} and the conditions.
    * @throws ProofInputException Occurred Exception.
    */
   protected List<Triple<JavaDLTerm, Set<JavaDLTerm>, Node>> computeResultsAndConditions(Services services, 
                                                                             Goal goal, 
                                                                             ProofEnvironment sideProofEnvironment,
                                                                             Sequent sequentToProve, 
                                                                             Function newPredicate) throws ProofInputException {
      return SymbolicExecutionSideProofUtil.computeResultsAndConditions(services, 
                                                       goal.proof(), 
                                                       sideProofEnvironment,
                                                       sequentToProve, 
                                                       newPredicate, 
                                                       "Side proof rule on node " + goal.node().serialNr() + ".", 
                                                       StrategyProperties.METHOD_CONTRACT,
                                                       StrategyProperties.LOOP_INVARIANT,
                                                       StrategyProperties.QUERY_ON,
                                                       StrategyProperties.SPLITTING_DELAYED,
                                                       true);
   }
   
   /**
    * Replaces the {@link JavaDLTerm} defined by the given {@link PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>}
    * with the given new {@link JavaDLTerm}.
    * @param pio The {@link PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>>} which defines the {@link JavaDLTerm} to replace.
    * @param newTerm The new {@link JavaDLTerm}.
    * @return The created {@link SequentFormula} in which the {@link JavaDLTerm} is replaced.
    */
   protected static SequentFormula<JavaDLTerm> replace(PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pio, JavaDLTerm newTerm, Services services) {
      // Iterate along the PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> and collect the parents and indices
      Deque<Pair<Integer, JavaDLTerm>> indexAndParents = new LinkedList<Pair<Integer, JavaDLTerm>>();
      JavaDLTerm root = pio.sequentFormula().formula();
      final PosInTerm<JavaDLTerm> pit = pio.posInTerm();
      for (int i = 0, sz=pit.depth(); i<sz; i++) { 
         int next = pit.getIndexAt(i);
         indexAndParents.addFirst(new Pair<Integer, JavaDLTerm>(Integer.valueOf(next), root));
         root = root.sub(next);
      }
      // Iterate over the collected parents and replace terms
      root = newTerm;
      for (Pair<Integer, JavaDLTerm> pair : indexAndParents) {
         JavaDLTerm parent = pair.second;
         JavaDLTerm[] newSubs = parent.subs().toArray(new JavaDLTerm[parent.arity()]);
         newSubs[pair.first] = root;
         root =  services.getTermFactory().createTerm(parent.op(), newSubs, parent.boundVars(), parent.modalContent(), parent.getLabels());
      }
      return new SequentFormula<>(root);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isApplicableOnSubTerms() {
      return false;
   }
}