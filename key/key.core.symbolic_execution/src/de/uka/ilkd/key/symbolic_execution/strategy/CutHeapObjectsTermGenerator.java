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

package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

import org.key_project.common.core.logic.calculus.SequentFormula;
import org.key_project.common.core.logic.op.Function;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

/**
 * This {@link TermGenerator} is used by the {@link SymbolicExecutionStrategy}
 * to add early alias checks of used objects as target of store operations
 * on heaps. To achieve this, this {@link TermGenerator} generates equality
 * {@link JavaDLTerm}s for each possible combination of objects.
 * @author Martin Hentschel
 */
public class CutHeapObjectsTermGenerator implements TermGenerator {
   /**
    * {@inheritDoc}
    */
   @Override
   public Iterator<JavaDLTerm> generate(RuleApp app, PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pos, Goal goal) {
      // Compute collect terms of sequent formulas
      Sequent sequent = goal.sequent();
      Set<JavaDLTerm> topTerms = new LinkedHashSet<JavaDLTerm>();
      for (SequentFormula<JavaDLTerm> sf : sequent) {
         topTerms.add(sf.formula());
      }
      // Compute equality terms
      HeapLDT heapLDT = goal.node().proof().getServices().getTheories().getHeapLDT();
      Set<JavaDLTerm> equalityTerms = new LinkedHashSet<JavaDLTerm>();
      for (SequentFormula<JavaDLTerm> sf : sequent) {
         collectEqualityTerms(sf, equalityTerms, topTerms, heapLDT, goal.node().proof().getServices());
      }
      return equalityTerms.iterator();
   }
   
   /**
    * Computes all possible equality terms between objects in the given {@link SequentFormula}.
    * @param sf The {@link SequentFormula} to work with.
    * @param equalityTerms The result {@link Set} with the equality {@link JavaDLTerm}s to fill.
    * @param topTerms The terms of all sequent formulas
    * @param heapLDT The {@link HeapLDT} to use.
    * @param services TODO
    */
   protected void collectEqualityTerms(SequentFormula<JavaDLTerm> sf, Set<JavaDLTerm> equalityTerms, Set<JavaDLTerm> topTerms, HeapLDT heapLDT, Services services) {
      // Collect objects (target of store operations on heap)
      Set<JavaDLTerm> storeLocations = new LinkedHashSet<JavaDLTerm>();
      collectStoreLocations(sf.formula(), storeLocations, heapLDT);
      // Check if equality checks are possible
      if (storeLocations.size() >= 2) {
         // Generate all possible equality checks
         JavaDLTerm[] storeLocationsArray = storeLocations.toArray(new JavaDLTerm[storeLocations.size()]);
         for (int i = 0; i < storeLocationsArray.length; i++) {
            for (int j = i + 1; j < storeLocationsArray.length; j++) {
               JavaDLTerm equality = services.getTermBuilder().equals(storeLocationsArray[i], storeLocationsArray[j]);
               if (!topTerms.contains(equality)) {
                  JavaDLTerm negatedEquality = services.getTermBuilder().not(equality); // The not is because the order of the branches is nicer (assumption: default case that objects are different is shown in symbolic execution trees on the left)
                  if (!topTerms.contains(negatedEquality)) {
                     equalityTerms.add(negatedEquality); // Do equality cut only if knowledge is not already part of the sequent
                  }
               }
            }
         }
      }
   }

   /**
    * Collects recursive all possible targets of store operations on a heap.
    * @param term The {@link JavaDLTerm} to start search in.
    * @param storeLocations The result {@link Set} to fill.
    * @param heapLDT The {@link HeapLDT} to use (it provides the store and create {@link Function}).
    */
   protected void collectStoreLocations(JavaDLTerm term, final Set<JavaDLTerm> storeLocations, final HeapLDT heapLDT) {
      term.execPreOrder(new DefaultVisitor() {
         @Override
         public void visit(JavaDLTerm visited) {
            if (visited.op() == heapLDT.getStore()) {
               storeLocations.add(visited.sub(1));
            }
         }
      });
   }
}
