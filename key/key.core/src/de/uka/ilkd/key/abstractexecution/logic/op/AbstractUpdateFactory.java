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
package de.uka.ilkd.key.abstractexecution.logic.op;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstrUpdateLHS;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AllLocsLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.FieldLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.HasToLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.PVLoc;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.SkolemLoc;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Factory class for {@link AbstractUpdate}s and {@link AbstractUpdate} LHSs /
 * RHSs.
 *
 * @author Dominic Steinhoefel
 */
public class AbstractUpdateFactory {
    public static final AbstractUpdateFactory INSTANCE = new AbstractUpdateFactory();

    /**
     * Singleton constructor.
     */
    private AbstractUpdateFactory() {
    }

    /**
     * TODO
     *
     * @param t
     * @param ec
     * @param services
     * @return
     */
    public Set<AbstractUpdateLoc> abstractUpdateLocsFromLocSetUnionTerm(Term t,
            ExecutionContext ec, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        return tb.locsetUnionToSet(t).stream()
                .map(sub -> abstractUpdateLocFromTerm(sub, ec, services))
                .collect(Collectors.toCollection(() -> new LinkedHashSet<>()));
    }

    /**
     * TODO
     *
     * @param t
     * @param ec
     * @param services
     * @return
     */
    public AbstractUpdateLoc abstractUpdateLocFromTerm(Term t,
            ExecutionContext ec, Services services) {
        final LocSetLDT locSetLDT = services.getTypeConverter().getLocSetLDT();
        final TermBuilder tb = services.getTermBuilder();
        final TypeConverter tc = services.getTypeConverter();

        final Operator op = t.op();

        if (op instanceof LocationVariable) {
            return new PVLoc((LocationVariable) op);
        } else if (t.op() == locSetLDT.getAllLocs()) {
            return new AllLocsLoc(locSetLDT.getAllLocs());
        } else if (op instanceof Function && op.arity() == 0
                && ((Function) op).sort() == locSetLDT.targetSort()) {
            return new SkolemLoc((Function) op);
        } else if (op == locSetLDT.getSingletonPV()) {
            return abstractUpdateLocFromTerm(t.sub(0), ec, services);
        } else if (op == locSetLDT.getHasTo()) {
            final AbstractUpdateLoc subResult = abstractUpdateLocFromTerm(
                    t.sub(0), ec, services);
            assert subResult instanceof AbstrUpdateLHS;
            return new HasToLoc((AbstrUpdateLHS) subResult);
        } else if (op == locSetLDT.getSingleton()) {
            Term obj = t.sub(0);
            final Term field = t.sub(1);
            if (obj.toString().equals("self")) {
                obj = tc.findThisForSort(obj.sort(), ec);
            }
            final Term selectTerm = tb.select(
                    services.getJavaInfo().objectSort(), tb.getBaseHeap(), obj,
                    field);
            return fieldLocFromSelectTerm(selectTerm, tc, ec);
        } else if (services.getTypeConverter().getHeapLDT().isSelectOp(op)) {
            return fieldLocFromSelectTerm(t, tc, ec);
        } else {
            assert false : "Unexpected element of loc set union.";
            return null;
        }
    }

    /**
     * TODO
     *
     * @param selectTerm
     * @param tc
     * @param ec
     * @return
     */
    private AbstractUpdateLoc fieldLocFromSelectTerm(final Term selectTerm,
            final TypeConverter tc, ExecutionContext ec) {
        final Expression pe = tc.convertToProgramElement(selectTerm);
        if (pe instanceof FieldReference) {
            return new FieldLoc((FieldReference) pe, ec);
        } else if (pe instanceof ProgramVariable) {
            return new FieldLoc(new FieldReference((ProgramVariable) pe, null),
                    ec);
        } else {
            assert false : "Unexpected Expression type as result of field conversion";
            return null;
        }
    }
}
