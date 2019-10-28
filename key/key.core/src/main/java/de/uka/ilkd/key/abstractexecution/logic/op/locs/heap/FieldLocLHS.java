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
package de.uka.ilkd.key.abstractexecution.logic.op.locs.heap;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.NullSort;

/**
 * A field location for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class FieldLocLHS extends HeapLocLHS {
    private final Term objTerm;
    // XXX (DS, 2019-10-22): If possible, switch from LocationVariable to Term here,
    // since it's quite questionable to use this "canonical program variable" for
    // which one has to rely on a specific name of the field, which won't work in
    // general, e.g. in hand-written KeY files.
    private final LocationVariable fieldPV;

    public FieldLocLHS(Term objTerm, LocationVariable fieldPV) {
        this.objTerm = objTerm;
        this.fieldPV = fieldPV;
    }

    @Override
    public Term toTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();

        return tb.singleton(objTerm, tb.func(heapLDT.getFieldSymbolForPV(fieldPV, services)));
    }

    @Override
    public Set<Operator> childOps() {
        final Set<Operator> result = new LinkedHashSet<>();
        result.add(fieldPV);

        final OpCollector opColl = new OpCollector();
        objTerm.execPostOrder(opColl);
        result.addAll(opColl.ops());

        return result;
    }

    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc, Services services) {
        /*
         * The comparison to the name of the base heap is ugly, but for now, I would
         * rather not also pass the services object here...
         */
        return (otherLoc instanceof PVLoc && ((PVLoc) otherLoc).getVar()
                .equals(services.getTypeConverter().getHeapLDT().getHeap()))
                || (otherLoc instanceof FieldLocLHS
                        && ((FieldLocLHS) otherLoc).objTerm.equals(this.objTerm)
                        && ((FieldLocLHS) otherLoc).fieldPV.equals(this.fieldPV));
    }

    /**
     * @return true iff this is a static location.
     */
    public boolean isStatic() {
        return objTerm.op() instanceof Function
                && ((Function) objTerm.op()).sort() instanceof NullSort;
    }

    @Override
    public String toString() {
        return String.format("%s.%s",
                isStatic() ? fieldPV.getContainerType().getName() : objTerm.toString(),
                ((ProgramElementName) fieldPV.name()).getProgramName());
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof FieldLocLHS && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 7 * objTerm.hashCode() + 11 * fieldPV.hashCode();
    }

}
