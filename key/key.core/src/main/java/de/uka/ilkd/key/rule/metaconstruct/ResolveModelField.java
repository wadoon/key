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

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import java.util.ArrayList;
import java.util.List;


/**
 * This meta construct resolves a model field reference to a call of the corresponding observer.
 *
 * @author Mattias Ulbrich
 */
public final class ResolveModelField extends AbstractTermTransformer {

    public ResolveModelField() {
        super(new Name("#resolveModelField"), 2);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, Services services ) {

        Term receiver = term.sub(0);
        Term field = term.sub(1);

        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        Operator op = field.op();
        Function observer;
        if (op instanceof ObserverFunction) {
            observer = (Function) op;
        } else {
            observer = heapLDT.getFieldSymbolForPV((LocationVariable) op, services);
        }

        List<Term> args = new ArrayList<>();
        args.add(services.getTermBuilder().var(heapLDT.getHeap()));
        if (observer.argSorts().size() == 2) {
            args.add(receiver);
        }

        return services.getTermFactory().createTerm(observer, args);
    }
}
