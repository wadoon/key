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

import java.util.Set;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A field location for use in an {@link AbstractUpdate}.
 * 
 * TODO Currently no explicit support for static fields.
 *
 * @author Dominic Steinhoefel
 */
public class FieldLoc extends HeapLoc {
    private final Term objTerm;
    private final Term fieldTerm;
    private final Sort sort;

    public FieldLoc(Term objTerm, Term fieldTerm, Services services) {
        this.objTerm = objTerm;
        this.fieldTerm = fieldTerm;

        Sort sort = null;
        try {
            sort = ((ProgramVariable) services.getTypeConverter().getHeapLDT()
                    .translateTerm(fieldTerm, null, services)).sort();
        } catch (Exception e) {
            sort = services.getJavaInfo().objectSort();
        }
        this.sort = sort;
    }

    /*
     * Maybe interesting for getting correct self term (where it's converted):
     * services.getTypeConverter().findThisForSort( pm.getContainerType().getSort(),
     * execContext) (see MethodCall class)
     */

    @Override
    public Term toTerm(Services services) {
        final TermBuilder tb = services.getTermBuilder();
        return tb.singleton(objTerm, fieldTerm);
    }

    /**
     * @return the objTerm
     */
    public Term getObjTerm() {
        return objTerm;
    }

    /**
     * @return the fieldTerm
     */
    public Term getFieldTerm() {
        return fieldTerm;
    }

    @Override
    public Set<Operator> childOps() {
        final OpCollector opColl = new OpCollector();
        objTerm.execPostOrder(opColl);
        fieldTerm.execPostOrder(opColl);
        return opColl.ops();
    }

    @Override
    public boolean mayAssign(AbstractUpdateLoc otherLoc, Services services) {
        return (otherLoc instanceof PVLoc && ((PVLoc) otherLoc).getVar()
                .equals(services.getTypeConverter().getHeapLDT().getHeap()))
                || (otherLoc instanceof FieldLoc
                        && ((FieldLoc) otherLoc).objTerm.equals(this.objTerm)
                        && ((FieldLoc) otherLoc).fieldTerm.equals(this.fieldTerm));
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
        return String.format("%s.%s", objTerm, HeapLDT.getPrettyFieldName(fieldTerm.op()));
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof FieldLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 7 * objTerm.hashCode() + 11 * fieldTerm.hashCode();
    }

    @Override
    public Sort sort() {
        return sort;
    }

    @Override
    public boolean isAbstract() {
        return false;
    }

}
