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

package de.uka.ilkd.key.proof;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramLocationsCollector;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;

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

    public TermAccessibleLocationsCollector(final Services services) {
        this.services = services;
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
            result.add(new SkolemLoc((Function) t.sub(0).op()));
        }

        final Function allLocs = services.getTypeConverter().getLocSetLDT().getAllLocs();
        if (t.op() == allLocs) {
            result.add(new AllLocsLoc(allLocs));
        }

//        final java.util.function.Function<Term, Set<AbstractUpdateLoc>> subToLoc = //
//                sub -> AbstractUpdateFactory.abstrUpdateLocsFromTermSafe( //
//                        sub, Optional.empty(), services);
//
//        if (t.op() instanceof Function
//                && services.abstractUpdateFactory().isAbstractPathCondition((Function) t.op())) {
//            t.subs().stream().map(subToLoc).forEach(result::addAll);
//        } else if (t.op() instanceof AbstractUpdate) {
//            t.subs().stream().map(subToLoc).forEach(result::addAll);
//        }

        if (!t.javaBlock().isEmpty()) {
            final ProgramLocationsCollector pvc = new ProgramLocationsCollector(
                    t.javaBlock().program(), services);
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
