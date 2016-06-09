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

package de.uka.ilkd.key.symbolic_execution.object_model;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.JavaDLTerm;

/**
 * An equivalence class which defines which {@link JavaDLTerm}s represent
 * the same {@link ISymbolicObject} in an {@link ISymbolicLayout}.
 * @author Martin Hentschel
 */
public interface ISymbolicEquivalenceClass extends ISymbolicElement {
   /**
    * Returns the terms which represents the same {@link ISymbolicObject}.
    * @return The terms which represents the same {@link ISymbolicObject}.
    */
   public ImmutableList<JavaDLTerm> getTerms();
   
   /**
    * Checks if a {@link JavaDLTerm} is contained.
    * @param term The {@link JavaDLTerm} to check.
    * @return {@code true} {@link JavaDLTerm} is contained, {@code false} {@link JavaDLTerm} is not contained.
    */
   public boolean containsTerm(JavaDLTerm term);
   
   /**
    * Returns the terms which represents the same {@link ISymbolicObject} as human readable {@link String}.
    * @return The terms which represents the same {@link ISymbolicObject} as human readable {@link String}.
    */
   public ImmutableList<String> getTermStrings();
   
   /**
    * Returns the most representative term.
    * @return The most representative term.
    */
   public JavaDLTerm getRepresentative();

   /**
    * Returns the most representative term as human readable {@link String}.
    * @return The most representative term as human readable {@link String}.
    */
   public String getRepresentativeString();
}