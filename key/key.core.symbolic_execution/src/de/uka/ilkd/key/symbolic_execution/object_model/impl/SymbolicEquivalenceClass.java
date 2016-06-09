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

package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;

/**
 * Default implementation of {@link ISymbolicEquivalenceClass}.
 * @author Martin Hentschel
 */
public class SymbolicEquivalenceClass extends AbstractElement implements ISymbolicEquivalenceClass {
   /**
    * The {@link Services} to use.
    */
   private final Services services;
   
   /**
    * The contained {@link JavaDLTerm}s which represents the same {@link ISymbolicObject}.
    */
   private ImmutableList<JavaDLTerm> terms;

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param settings The {@link IModelSettings} to use.
    */
   public SymbolicEquivalenceClass(Services services, IModelSettings settings) {
      this(services, ImmutableSLList.<JavaDLTerm>nil(), settings);
   }

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param terms The contained {@link JavaDLTerm}s which represents the same {@link ISymbolicObject}.
    * @param settings The {@link IModelSettings} to use.
    */
   public SymbolicEquivalenceClass(Services services, ImmutableList<JavaDLTerm> terms, IModelSettings settings) {
      super(settings);
      this.services = services;
      this.terms = terms;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<JavaDLTerm> getTerms() {
      return terms;
   }
   
   /**
    * Adds a new {@link JavaDLTerm}.
    * @param value The new {@link JavaDLTerm} to add.
    */
   public void addTerm(JavaDLTerm term) {
      terms = terms.append(term);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean containsTerm(JavaDLTerm term) {
      return terms.contains(term);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<String> getTermStrings() {
      ImmutableList<String> strings = ImmutableSLList.nil();
      for (JavaDLTerm term : terms) {
         strings = strings.append(formatTerm(term, services));
      }
      return strings;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public JavaDLTerm getRepresentative() {
      // Prefer null if contained in equivalence class
      final HeapLDT heapLDT = services.getTheories().getHeapLDT();
      JavaDLTerm nullTerm = CollectionUtil.search(terms, new IFilter<JavaDLTerm>() {
         @Override
         public boolean select(JavaDLTerm element) {
            return element.op() == heapLDT.getNull();
         }
      });
      if (nullTerm != null) {
         return nullTerm;
      }
      else {
         // Prefer terms which are a program variable
         JavaDLTerm representative = CollectionUtil.search(terms, new IFilter<JavaDLTerm>() {
            @Override
            public boolean select(JavaDLTerm element) {
               return element.op() instanceof IProgramVariable;
            }
         });
         return representative != null ? 
                representative : // Return term with program variable 
                terms.head(); // Return the first term
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getRepresentativeString() {
      JavaDLTerm representative = getRepresentative();
      if (representative != null) {
         return formatTerm(representative, services);
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "Equivalence Class " + getTermStrings();
   }
}