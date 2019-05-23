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
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
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
    protected Term toTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.singleton(objTerm, tb.var(fieldPV));
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
    public boolean mayAssign(AbstractUpdateLoc otherLoc) {
        return otherLoc instanceof FieldLocRHS
                && ((FieldLocRHS) otherLoc).getObjTerm().equals(this.objTerm)
                && ((FieldLocRHS) otherLoc).getFieldPV().equals(this.fieldPV);
    }

    @Override
    public String toString() {
        return String.format("%s.%s", objTerm,
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
