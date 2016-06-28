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

package org.key_project.bytecode.core.theories;

import org.key_project.bytecode.core.logic.Term;
import org.key_project.bytecode.core.logic.services.BCTermServices;
import org.key_project.common.core.theories.CCIntegerTheory;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 */
public class IntegerTheory extends CCIntegerTheory<Term> {

    /**
     * TODO: Document.
     *
     * @param services
     */
    protected IntegerTheory(BCTermServices services) {
        super(services);
    }

}
