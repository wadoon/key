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
package de.uka.ilkd.key.abstractexecution.logic.op.locs;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ProgVarReplacer;

/**
 * A field location for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class FieldLoc implements HeapLoc {
    private final Sort sort;
    private final Optional<Term> heapTerm;
    private final Term objTerm;
    private final LocationVariable fieldPV;
    private final LocationVariable heapVar;

    public FieldLoc(Optional<Sort> sort, Optional<Term> heapTerm, Term objTerm,
            LocationVariable fieldPV, LocationVariable heapVar) {
        this.sort = sort.orElse(fieldPV.sort());
        this.heapTerm = heapTerm;
        this.objTerm = objTerm;
        this.fieldPV = fieldPV;
        this.heapVar = heapVar;
    }

    @Override
    public Term toTerm(Services services) {
        return services.getTermBuilder().select(sort,
                heapTerm.orElse(services.getTermBuilder().getBaseHeap()),
                objTerm, fieldPV);
    }

    @Override
    public AbstractUpdateLoc replaceVariables(
            Map<ProgramVariable, ProgramVariable> replMap, Services services) {
        final ProgVarReplacer pvr = new ProgVarReplacer(replMap, services);

        final LocationVariable lHeapVar = Optional
                .ofNullable(replMap.get(heapVar))
                .map(LocationVariable.class::cast).orElse(heapVar);
        final LocationVariable lFieldPV = Optional
                .ofNullable(replMap.get(fieldPV))
                .map(LocationVariable.class::cast).orElse(fieldPV);
        final Optional<Term> lHeapTerm = heapTerm.map(t -> pvr.replace(t));
        final Term lObjTerm = pvr.replace(objTerm);

        return new FieldLoc(Optional.of(sort), lHeapTerm, lObjTerm, lFieldPV,
                lHeapVar);
    }

    @Override
    public Set<Operator> childOps() {
        final Set<Operator> result = new LinkedHashSet<>();
        result.add(heapVar);
        result.add(fieldPV);

        final OpCollector opColl = new OpCollector();
        heapTerm.ifPresent(t -> t.execPostOrder(opColl));
        objTerm.execPostOrder(opColl);
        result.addAll(opColl.ops());

        return result;
    }

    @Override
    public AbstrUpdateUpdatableLoc toUpdatableRHS() {
        return this;
    }
    
    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc) {
        return otherLoc instanceof FieldLoc && otherLoc.equals(this);
    }

    @Override
    public String toString() {
        return String.format("%s.%s", objTerm,
                ((ProgramElementName) fieldPV.name()).getProgramName());
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof FieldLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 7 * objTerm.hashCode() + 11 * fieldPV.hashCode();
    }

}
