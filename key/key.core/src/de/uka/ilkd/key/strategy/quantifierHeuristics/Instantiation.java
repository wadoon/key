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

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.LinkedHashMap;
import java.util.Map;

import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.Quantifier;
import org.key_project.common.core.logic.op.SortDependingFunction;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

class Instantiation {


   /** universally quantifiable variable bound in<code>allTerm</code> */
   private final QuantifiableVariable firstVar;

   private final JavaDLTerm matrix;

   /**
    * Literals occurring in the sequent at hand. This is used for branch
    * prediction
    */
   private ImmutableSet<JavaDLTerm> assumedLiterals = DefaultImmutableSet
         .<JavaDLTerm> nil();

   /** HashMap from instance(<code>JavaDLTerm</code>) to cost <code>Long</code> */
   private final Map<JavaDLTerm, Long> instancesWithCosts = new LinkedHashMap<JavaDLTerm, Long>();

   /** the <code>TriggersSet</code> of this <code>allTerm</code> */
   private final TriggersSet triggersSet;

   private Instantiation(JavaDLTerm allterm, Sequent seq, Services services) {
      firstVar = allterm.varsBoundHere(0).get(0);
      matrix = TriggerUtils.discardQuantifiers(allterm);
      /* Terms bound in every formula on <code>goal</code> */
      triggersSet = TriggersSet.create(allterm, services);
      assumedLiterals = initAssertLiterals(seq, services);
      addInstances(sequentToTerms(seq), services);
   }

   private static JavaDLTerm lastQuantifiedFormula = null;
   private static Sequent lastSequent = null;
   private static Instantiation lastResult = null;

   static Instantiation create(JavaDLTerm qf, Sequent seq, Services services) {	
      synchronized(Instantiation.class) {
         if (qf == lastQuantifiedFormula && seq == lastSequent)
            return lastResult;
      }
      final Instantiation result = new Instantiation(qf, seq, services);
      synchronized(Instantiation.class) {
         lastQuantifiedFormula = qf;
         lastSequent = seq;
         lastResult = new Instantiation(qf, seq, services);
      }
      return result;
   }

   private static ImmutableSet<JavaDLTerm> sequentToTerms(Sequent seq) {
      ImmutableList<JavaDLTerm> res = ImmutableSLList.<JavaDLTerm> nil();
      for (final SequentFormula cf : seq) {
         res = res.prepend(cf.formula());
      }
      return DefaultImmutableSet.fromImmutableList(res);
   }

   /**
    * @param terms
    *            on which trigger are doning matching search every
    *            <code>Substitution</code> s by matching <code>triggers</code>
    *            from <code>triggersSet</code> to <code>terms</code> compute
    *            their cost and store the pair of instance (JavaDLTerm) and
    *            cost(Long) in <code>instancesCostCache</code>
    */
   private void addInstances(ImmutableSet<JavaDLTerm> terms, Services services) {
      for (final Trigger t : triggersSet.getAllTriggers()) {
         for (final Substitution sub : t.getSubstitutionsFromTerms(terms,
               services)) {
            addInstance(sub, services);
         }
      }
      // if ( instancesWithCosts.isEmpty () )
      // ensure that there is always at least one instantiation
      // addArbitraryInstance ();
   }

   private void addArbitraryInstance(Services services) {
      ImmutableMap<QuantifiableVariable, JavaDLTerm> varMap = DefaultImmutableMap
            .<QuantifiableVariable, JavaDLTerm> nilMap();

      for (QuantifiableVariable quantifiableVariable : triggersSet
            .getUniQuantifiedVariables()) {
         final QuantifiableVariable v = quantifiableVariable;
         final JavaDLTerm inst = createArbitraryInstantiation(v, services);
         varMap = varMap.put(v, inst);
      }

      addInstance(new Substitution(varMap), services);
   }

   private JavaDLTerm createArbitraryInstantiation(QuantifiableVariable var,
         TermServices services) {
      return services.getTermBuilder().func (var.sort().getCastSymbol (services),
            services.getTermBuilder().zero());
   }

   private void addInstance(Substitution sub, Services services) {
      final long cost = PredictCostProver.computerInstanceCost(sub,
            getMatrix(), assumedLiterals, services);
      if (cost != -1)
         addInstance(sub, cost);
   }

   /**
    * add instance of <code>var</code> in <code>sub</code> with
    * <code>cost</code> to <code>instancesCostCache</code> if this instance is
    * exist, compare thire cost and store the less one.
    * 
    * @param sub
    * @param cost
    */
   private void addInstance(Substitution sub, long cost) {
      final JavaDLTerm inst = sub.getSubstitutedTerm(firstVar);
      final Long oldCost = instancesWithCosts.get(inst);
      if (oldCost == null || oldCost.longValue() >= cost)
         instancesWithCosts.put ( inst, Long.valueOf ( cost ) );
   }

   /**
    * @param seq
    * @param services TODO
    * @return all literals in antesequent, and all negation of literal in
    *         succedent
    */
   private ImmutableSet<JavaDLTerm> initAssertLiterals(Sequent seq, TermServices services) {
      ImmutableSet<JavaDLTerm> assertLits = DefaultImmutableSet.<JavaDLTerm> nil();
      for (final SequentFormula cf : seq.antecedent()) {
         final JavaDLTerm atom = cf.formula();
         final Operator op = atom.op();
         if ( !( op == Quantifier.ALL || op == Quantifier.EX ) )
            assertLits = assertLits.add(atom);
      }
      for (final SequentFormula cf : seq.succedent()) {
         final JavaDLTerm atom = cf.formula();
         final Operator op = atom.op();
         if ( !( op == Quantifier.ALL || op == Quantifier.EX ) )
            assertLits = assertLits.add(services.getTermBuilder().not(atom));
      }
      return assertLits;
   }

   /**
    * Try to find the cost of an instance(inst) according its quantified
    * formula and current goal.
    */
   static RuleAppCost computeCost(JavaDLTerm inst, JavaDLTerm form, Sequent seq,
         Services services) {
      return Instantiation.create(form, seq, services).computeCostHelp(inst);
   }

   private RuleAppCost computeCostHelp(JavaDLTerm inst) {
      Long cost = instancesWithCosts.get(inst);
      if ( cost == null && ( inst.op () instanceof SortDependingFunction
            && ((SortDependingFunction)inst.op()).getKind().equals(Sort.CAST_NAME)) )
         cost = instancesWithCosts.get(inst.sub(0));

      if (cost == null) {
         // if (triggersSet)
         return TopRuleAppCost.INSTANCE;
      }
      if (cost.longValue() == -1)
         return TopRuleAppCost.INSTANCE;

      return NumberRuleAppCost.create(cost.longValue());
   }

   /** get all instances from instancesCostCache subsCache */
   ImmutableSet<JavaDLTerm> getSubstitution() {
      ImmutableSet<JavaDLTerm> res = DefaultImmutableSet.<JavaDLTerm> nil();
      for (final JavaDLTerm inst : instancesWithCosts.keySet()) {
         res = res.add(inst);
      }
      return res;
   }

   private JavaDLTerm getMatrix() {
      return matrix;
   }

}