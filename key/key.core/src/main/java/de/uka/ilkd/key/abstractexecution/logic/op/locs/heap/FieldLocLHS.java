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
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateAssgnLoc;
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
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.proof.ProgVarReplacer;

/**
 * A field location for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class FieldLocLHS extends HeapLocLHS {
    private final Term objTerm;
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
    public AbstractUpdateAssgnLoc replaceVariables(Map<ProgramVariable, ProgramVariable> replMap,
            Services services) {
        final ProgVarReplacer pvr = new ProgVarReplacer(replMap, services);

        final LocationVariable lFieldPV = Optional.ofNullable(replMap.get(fieldPV))
                .map(LocationVariable.class::cast).orElse(fieldPV);
        final Term lObjTerm = pvr.replace(objTerm);

        return new FieldLocLHS(lObjTerm, lFieldPV);
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
                || (otherLoc instanceof FieldLocRHS
                        && ((FieldLocRHS) otherLoc).getObjTerm().equals(this.objTerm)
                        && ((FieldLocRHS) otherLoc).getFieldPV().equals(this.fieldPV));
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
