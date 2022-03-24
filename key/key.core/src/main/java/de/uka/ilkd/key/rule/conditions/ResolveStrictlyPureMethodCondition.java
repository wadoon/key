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

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import org.key_project.util.collection.ImmutableArray;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;


/**
 * This variable condition stores a pure method invocation into a schema variable.
 *
 * \strictlyPureMethodCall(#rp, #mn, #selist, result)
 *
 * stores the resolved term "#rp.#mn(#selist)" into result. Quite a bit of translation involved.
 *
 * Negation is not supported.
 *
 * @author Mattias Ulbrich
 */
public final class ResolveStrictlyPureMethodCondition implements VariableCondition {

    private final SchemaVariable caller;
    private final SchemaVariable methname;
    private final SchemaVariable args;
    private final SchemaVariable target;

    public ResolveStrictlyPureMethodCondition(SchemaVariable caller, SchemaVariable methname,
                                              SchemaVariable args, SchemaVariable target) {
        this.caller = caller;
        this.methname = methname;
        this.args = args;
        this.target = target;
    }

    private static ImmutableArray<Expression> toExpArray(ImmutableArray<? extends ProgramElement> a) {
        Expression[] result = new Expression[a.size()];
        for (int i = 0; i < a.size(); i++) {
            result[i] = (Expression) a.get(i);
        }
        return new ImmutableArray<>(result);
    }

    @SuppressWarnings("unchecked")
    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
                                 MatchConditions mc, Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        ReferencePrefix rp;
        if (var == caller) {
            rp = (ReferencePrefix) instCandidate;
        } else {
            rp = (ReferencePrefix) svInst.getInstantiation(caller);
        }

        MethodName mn;
        if (var == methname) {
            mn = (MethodName) instCandidate;
        } else {
            mn = (MethodName) svInst.getInstantiation(methname);
        }

        ImmutableArray<ProgramElement> ape;
        if (var == args) {
            ape = (ImmutableArray<ProgramElement>) instCandidate;
        } else {
            ape = (ImmutableArray<ProgramElement>) svInst.getInstantiation(args);
        }

        if (rp == null || mn == null || ape == null) {
            return mc;
        }

        IProgramMethod method = getMethod(rp, mn, ape, svInst, services);

        if (method == null) {
            return null;
        }

        if (method.isModel() || JMLInfoExtractor.isStrictlyPure(method)) {
            Term term = makeTerm(rp, method, ape, services, svInst.getExecutionContext());
            svInst = svInst.add(target, term, services);
            return mc.setInstantiations(svInst);
        }

        return null;
    }

    private Term makeTerm(ReferencePrefix rp, IProgramMethod method,
                          ImmutableArray<ProgramElement> ape, Services services,
                          ExecutionContext ec) {
        List<Term> args = new ArrayList<>();
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        if(method.argSorts().get(0) == heapLDT.targetSort()) {
            args.add(services.getTermFactory().createTerm(heapLDT.getHeap()));
        }
        if(!method.isStatic()) {
            Term receiver = toTerm(rp, ec, services);
            args.add(receiver);
        }
        for (ProgramElement pe : ape) {
            args.add(toTerm(pe, ec, services));
        }

        return services.getTermFactory().createTerm(method, args);
    }

    private static Term toTerm(ProgramElement pe, ExecutionContext ec, Services services) {
        return services.getTypeConverter().convertToLogicElement(pe, ec);
    }

    private IProgramMethod getMethod(ReferencePrefix rp, MethodName mn,
                                     ImmutableArray<? extends ProgramElement> ape,
                                     SVInstantiations svInst, Services services) {

        IProgramMethod method = null;

        if (rp != null && mn != null && ape != null) {
            ImmutableArray<Expression> ar = toExpArray(ape);
            ExecutionContext ec = svInst.getContextInstantiation().activeStatementContext();
            MethodReference mr = new MethodReference(ar, mn, rp);
            KeYJavaType prefixType;

            // static vs. instance method
            if (rp instanceof Expression) {
                prefixType = services.getTypeConverter().getKeYJavaType((Expression) rp, ec);
            } else {
                assert rp instanceof TypeRef;
                prefixType = ((TypeRef)rp).getKeYJavaType();
            }

            if (ec != null) {
                method = mr.method(services, prefixType, ec);
                // we are only interested in the signature. The method
                // must be declared in the static context.
            } else { //no execution context
                method = mr.method(services, prefixType,
                        mr.getMethodSignature(services, ec),
                        prefixType);
            }
        }
        return method;
    }


    @Override
    public String toString() {
        return String.format("\\strictlyPureMethodCall(%s, %s, %s, %s)",
                caller, methname, args, target);
    }

}