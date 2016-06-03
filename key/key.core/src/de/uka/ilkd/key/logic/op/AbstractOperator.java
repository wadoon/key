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

package de.uka.ilkd.key.logic.op;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;

/**
 * Abstract operator class offering some common functionality.<br/>
 * 
 * <strong>TODO:</strong> This should be named something like
 * "AbstractTypeCheckingAndInferenceService" and not be used for assembling
 * actual terms.
 */
abstract class AbstractOperator extends GenericAbstractOperator implements
        Operator, ExtendedTypeCheckingAndInferenceService {

    protected AbstractOperator(Name name, int arity,
            ImmutableArray<Boolean> whereToBind, boolean isRigid) {
        super(name, arity, whereToBind, isRigid);
    }

    protected AbstractOperator(Name name, int arity, Boolean[] whereToBind,
            boolean isRigid) {
        this(name, arity, new ImmutableArray<Boolean>(whereToBind), isRigid);
    }

    protected AbstractOperator(Name name, int arity, boolean isRigid) {
        this(name, arity, (ImmutableArray<Boolean>) null, isRigid);
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.ExtendedTypeCheckingAndInferenceService#additionalValidTopLevel(de.uka.ilkd.key.logic.Term)
     */
    @Override
    public abstract boolean additionalValidTopLevel(Term term);

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.ExtendedTypeCheckingAndInferenceService#validTopLevel(de.uka.ilkd.key.logic.Term)
     */
    @Override
    public boolean validTopLevel(Term term) {
        if (arity != term.arity() || arity != term.subs().size()
                || (whereToBind == null) != term.boundVars().isEmpty()) {
            return false;
        }

        for (int i = 0, n = arity; i < n; i++) {
            if (term.sub(i) == null) {
                return false;
            }
        }

        return additionalValidTopLevel(term);
    }
}