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

package org.key_project.bytecode.core.services;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.Sorted;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.TypeCheckingAndInferenceService;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

/**
 * This class is a STUB without any meaningful content. It's just been created
 * to allow for the creation of test terms at the very beginning of the
 * implementation.
 *
 * @author Dominic Scheurer
 */
public class TypeCheckingAndInferenceServiceImpl<O extends Operator> implements
        TypeCheckingAndInferenceService<O> {

    @Override
    public Sort sort(ImmutableArray<? extends CCTerm<?, ?, ?, ?>> terms, O op) {
        // TODO This is a STUB -- add real sort computation.
        return ((Sorted) op).sort();
    }

    @Override
    public boolean validTopLevel(CCTerm<?, ?, ?, ?> term, O op) {
        // TODO This is a STUB
        return true;
    }

}
