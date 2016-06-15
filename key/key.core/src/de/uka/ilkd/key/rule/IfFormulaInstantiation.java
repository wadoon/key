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

package de.uka.ilkd.key.rule;

import org.key_project.common.core.logic.calculus.SequentFormula;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JavaDLTerm;


/*
 * This interface represents objects representing an instantiation of
 * one formula of the if-sequence of a taclet.
 */

public interface IfFormulaInstantiation {

    /**
     * @return the cf this is pointing to
     */
    SequentFormula<JavaDLTerm> getConstrainedFormula ();

    String             toString              (Services services);
}