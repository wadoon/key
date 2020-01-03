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

package de.uka.ilkd.key.abstractexecution.proof;

import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramLocationsCollector;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;

/**
 * Collects the accessible locations in a {@link Term} (an over-approximation,
 * i.e., if a location will be overwritten before, this is not taken into
 * account). Locations in this sense are primarily program variables, but also
 * further entities used in <em>Abstract Execution</em>: Skolem location sets
 * and the allLocs ("everything") location symbol. Should be used for "Abstract
 * Execution-aware" simplifications instead of, e.g.,
 * {@link TermProgramVariableCollector}.
 * 
 * @author Dominic Steinhoefel
 */
public class TermAccessibleLocationsCollector extends DefaultVisitor {
    private final Set<AbstractUpdateLoc> result = new LinkedHashSet<>();
    private final Services services;
    private final GoalLocalSpecificationRepository localSpecRepo;

    public TermAccessibleLocationsCollector(GoalLocalSpecificationRepository localSpecRepo, final Services services) {
        this.services = services;
        this.localSpecRepo = localSpecRepo;
    }

    /**
     * is called by the execPostOrder-method of a term
     * 
     * @param t the Term to checked if it is a program variable and if true the
     *          variable is added to the list of found variables
     */
    public void visit(Term t) {
        if (t.op() instanceof LocationVariable) {
            result.add(new PVLoc((LocationVariable) t.op()));
        }

        if (AbstractExecutionUtils.isAbstractSkolemLocationSetValueTerm(t, services)) {
            result.addAll(AbstractUpdateFactory.abstrUpdateLocsFromUnionTerm(t.sub(0), Optional.empty(), services));
        }

        if (!t.javaBlock().isEmpty()) {
            final ProgramLocationsCollector pvc = new ProgramLocationsCollector(
                    t.javaBlock().program(), localSpecRepo, services);
            pvc.start();
            result.addAll(pvc.locations());
        }
    }

    /**
     * @return The extracted locations.
     */
    public Set<AbstractUpdateLoc> locations() {
        return result;
    }
}
