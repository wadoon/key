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

package de.uka.ilkd.key.logic;

/**
 * {@link GenericTerm} extension for Java terms, provides methods related to
 * contained Java statements.
 *
 * @author Dominic Scheurer
 */
public interface Term extends GenericTerm {

    /**
     * The Java block at top level.
     */
    public JavaBlock javaBlock();

    /**
     * Checks if the {@link Term} or one of its direct or indirect children
     * contains a non empty {@link JavaBlock}.
     * 
     * @return {@code true} The {@link Term} or one of its direct or indirect
     *         children contains a non empty {@link JavaBlock}, {@code false} no
     *         {@link JavaBlock} available.
     */
    public boolean isContainsJavaBlockRecursive();
}
