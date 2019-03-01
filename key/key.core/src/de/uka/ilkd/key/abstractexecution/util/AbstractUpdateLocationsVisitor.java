// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.util;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;

/**
 * This visitor extracts {@link AbstractUpdateLoc}s from a {@link Term}.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractUpdateLocationsVisitor extends DefaultVisitor {
    private final Set<AbstractUpdateLoc> result = new LinkedHashSet<>();
    private final AbstractUpdateFactory factory = AbstractUpdateFactory.INSTANCE;

    private final ExecutionContext ec;
    private final Services services;

    public AbstractUpdateLocationsVisitor(ExecutionContext ec,
            Services services) {
        this.ec = ec;
        this.services = services;
    }

    @Override
    public void visit(Term visited) {
        factory.tryExtractAbstrUpdateLocFromTerm(visited, ec, services)
                .ifPresent(this.result::add);
    }

    /**
     * @return The extracted locations.
     */
    public Set<AbstractUpdateLoc> getResult() {
        return result;
    }
}
