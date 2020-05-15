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

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdate;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A Skolem location set suitable for use in an {@link AbstractUpdate}.
 *
 * @author Dominic Steinhoefel
 */
public class ParametricSkolemLoc implements AbstractUpdateLoc {
    private final Function skFunc;
    private final Term[] params;

    public ParametricSkolemLoc(Function skFunc, Term[] params) {
        this.skFunc = skFunc;
        this.params = params;
    }

    @Override
    public Term toTerm(Services services) {
        return services.getTermBuilder().func(skFunc, params);
    }

    @Override
    public Set<Operator> childOps() {
        final OpCollector opColl = new OpCollector();

        Arrays.stream(params).forEach(p -> p.execPostOrder(opColl));

        final Set<Operator> result = new LinkedHashSet<>();
        result.add(skFunc);
        result.addAll(opColl.ops());

        return result;
    }
    
    public Function getSkFunc() {
        return skFunc;
    }
    
    public Term[] getParams() {
        return params;
    }

    @Override
    public String toString() {
        return String.format("%s(%s)", skFunc.toString(),
                Arrays.stream(params).map(Term::toString).collect(Collectors.joining(",")));
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof ParametricSkolemLoc && obj.hashCode() == hashCode();
    }

    @Override
    public int hashCode() {
        return 5 + 17 * skFunc.hashCode() + 27 * Arrays.hashCode(params);
    }

    @Override
    public Sort sort() {
        return skFunc.sort();
    }

    @Override
    public boolean isAbstract() {
        return true;
    }
}
