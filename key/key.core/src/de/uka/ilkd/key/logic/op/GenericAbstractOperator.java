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

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.Name;

/**
 * Abstract operator class offering some common functionality.<br/>
 * 
 * <strong>TODO:</strong> This should be named "AbstractOperator"; the previous
 * {@link AbstractOperator} interface should get the name
 * "AbstractTypeCheckingAndInferenceService" or the like.
 *
 * @author Dominic Scheurer
 */
public class GenericAbstractOperator implements GenericOperator {

    protected final Name name;
    protected final int arity;
    protected final ImmutableArray<Boolean> whereToBind;
    protected final boolean isRigid;

    protected GenericAbstractOperator(Name name, int arity,
            ImmutableArray<Boolean> whereToBind, boolean isRigid) {
        assert name != null;
        assert arity >= 0;
        assert whereToBind == null || whereToBind.size() == arity;
        this.name = name;
        this.arity = arity;
        this.whereToBind = whereToBind;
        this.isRigid = isRigid;
    }

    protected final ImmutableArray<Boolean> whereToBind() {
        return whereToBind;
    }

    @Override
    public final Name name() {
        return name;
    }

    @Override
    public final int arity() {
        return arity;
    }

    @Override
    public final boolean bindVarsAt(int n) {
        return whereToBind != null && whereToBind.get(n);
    }

    @Override
    public final boolean isRigid() {
        return isRigid;
    }

    @Override
    public String toString() {
        return name().toString();
    }

}