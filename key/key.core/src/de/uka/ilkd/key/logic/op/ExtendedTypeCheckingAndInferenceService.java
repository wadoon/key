// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Term;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
interface ExtendedTypeCheckingAndInferenceService extends Operator {

    /**
     * Allows subclasses to impose custom demands on what constitutes a valid
     * term using the operator represented by the subclass.
     */
    boolean additionalValidTopLevel(Term term);

    boolean validTopLevel(Term term);

}