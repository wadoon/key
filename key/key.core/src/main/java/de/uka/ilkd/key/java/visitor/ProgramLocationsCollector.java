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

package de.uka.ilkd.key.java.visitor;

import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.BlockContract;

/**
 * Walks through a java AST in depth-left-fist-order. This walker is used
 * collect all {@link AbstractUpdateLoc}s. Should be used instead of
 * {@link ProgramVariableCollector} for performing <em>Abstract
 * Execution-aware</em> simplifications, since not only program variables, but
 * also <em>abstract locations sets</em> play a role there.
 * 
 * @author Dominic Steinhoefel
 */
public class ProgramLocationsCollector extends ProgramVariableCollector {
    private final Set<AbstractUpdateLoc> locations = new LinkedHashSet<>();

    /**
     * collects all program variables occurring in the AST <tt>root</tt> using this
     * constructor is equivalent to <tt>ProggramVariableCollector(root, false)</tt>
     *
     * @param root     the ProgramElement which is the root of the AST
     * @param services the Services object
     */
    public ProgramLocationsCollector(ProgramElement root, Services services) {
        super(root, services);
    }

    /**
     * Returns resulting <em>location variables</em>; corresponds to (and calls)
     * {@link ProgramVariableCollector#result()}. Use {@link #locations()} to
     * receive the <em>locations</em> (because for that you're using this class,
     * right?).
     */
    @Override
    public LinkedHashSet<LocationVariable> result() {
        return super.result();
    }

    /**
     * @return The extracted locations.
     */
    public Set<AbstractUpdateLoc> locations() {
        locations.addAll(result().stream().map(PVLoc::new)
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>())));

        return locations;
    }

    @Override
    public void performActionOnAbstractProgramElementContract(BlockContract contract) {
        super.performActionOnAbstractProgramElementContract(contract);

        for (final LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            final Term accessibleClause = contract.getAccessibleClause(heap, services);
            if (accessibleClause != null) {
                locations.addAll(AbstractUpdateFactory.abstrUpdateLocsFromTerm( //
                        accessibleClause, Optional.empty(), services));
            }
        }
    }

    @Override
    public String toString() {
        return locations.toString();
    }
}
