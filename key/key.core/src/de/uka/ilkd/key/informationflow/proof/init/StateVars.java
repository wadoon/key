/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.informationflow.proof.init;

import java.util.Iterator;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Namespace;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;


/**
 * Prepare program and location variables.
 * <p/>
 * @author christoph
 * <p/>
 */
public class StateVars {

    public final ImmutableList<JavaDLTerm> termList;

    public final ImmutableList<JavaDLTerm> paddedTermList;

    public final JavaDLTerm self;

    public final JavaDLTerm guard;

    public final ImmutableList<JavaDLTerm> localVars;

    public final JavaDLTerm result;

    public final JavaDLTerm exception;

    public final JavaDLTerm heap;

    public final JavaDLTerm mbyAtPre;


    public StateVars(JavaDLTerm self,
                     JavaDLTerm guard,
                     ImmutableList<JavaDLTerm> localVars,
                     JavaDLTerm result,
                     JavaDLTerm exception,
                     JavaDLTerm heap,
                     JavaDLTerm mbyAtPre) {
        this.self = self;
        this.guard = guard;
        this.localVars = localVars;
        this.result = result;
        this.exception = exception;
        this.heap = heap;
        this.mbyAtPre = mbyAtPre;

        ImmutableList<JavaDLTerm> terms =
                ImmutableSLList.<JavaDLTerm>nil();
        terms = appendIfNotNull(terms, heap);
        terms = appendIfNotNull(terms, self);
        terms = appendIfNotNull(terms, guard);
        terms = appendIfNotNull(terms, localVars);
        terms = appendIfNotNull(terms, result);
        terms = appendIfNotNull(terms, exception);
        terms = appendIfNotNull(terms, mbyAtPre);
        termList = terms;

        ImmutableList<JavaDLTerm> allTerms =
                ImmutableSLList.<JavaDLTerm>nil();
        allTerms = allTerms.append(heap);
        allTerms = allTerms.append(self);
        allTerms = allTerms.append(guard);
        allTerms = allTerms.append(localVars);
        allTerms = allTerms.append(result);
        allTerms = allTerms.append(exception);
        allTerms = allTerms.append(mbyAtPre);
        paddedTermList = allTerms;
    }


    public StateVars(JavaDLTerm self,
                     ImmutableList<JavaDLTerm> localVars,
                     JavaDLTerm result,
                     JavaDLTerm exception,
                     JavaDLTerm heap,
                     JavaDLTerm mbyAtPre) {
        this(self, null, localVars, result, exception, heap, mbyAtPre);
    }


    private ImmutableList<JavaDLTerm> appendIfNotNull(ImmutableList<JavaDLTerm> list,
                                                JavaDLTerm t) {
        if (t != null) {
            return list.append(t);
        } else {
            return list;
        }
    }


    private ImmutableList<JavaDLTerm> appendIfNotNull(ImmutableList<JavaDLTerm> list,
                                                ImmutableList<JavaDLTerm> list2) {
        ImmutableList<JavaDLTerm> result = list;
        for (JavaDLTerm t : list2) {
            result = appendIfNotNull(result, t);
        }
        return result;
    }


    public StateVars(JavaDLTerm self,
                     JavaDLTerm guard,
                     ImmutableList<JavaDLTerm> localVars,
                     JavaDLTerm heap) {
        this(self, guard, localVars, null, null, heap, null);
    }


    public StateVars(JavaDLTerm self,
                     JavaDLTerm guard,
                     ImmutableList<JavaDLTerm> localVars,
                     JavaDLTerm result,
                     JavaDLTerm exception,
                     JavaDLTerm heap) {
        this(self, guard, localVars, result, exception, heap, null);
    }


    public StateVars(JavaDLTerm self,
                     ImmutableList<JavaDLTerm> localVars,
                     JavaDLTerm result,
                     JavaDLTerm exception,
                     JavaDLTerm heap) {
        this(self, localVars, result, exception, heap, null);
    }


    public StateVars(JavaDLTerm self,
                     ImmutableList<JavaDLTerm> localVars,
                     JavaDLTerm heap) {
        this(self, localVars, null, null, heap);
    }


    public StateVars(StateVars orig,
                     String postfix,
                     Services services) {
        this(copyVariable(orig.self, postfix, services),
             copyVariable(orig.guard, postfix, services),
             copyVariables(orig.localVars, postfix, services),
             copyVariable(orig.result, postfix, services),
             copyVariable(orig.exception, postfix, services),
             copyHeapSymbol(orig.heap, postfix, services),
             copyFunction(orig.mbyAtPre, postfix, services));
    }


    private static ImmutableList<JavaDLTerm> copyVariables(ImmutableList<JavaDLTerm> ts,
                                                     String postfix,
                                                     Services services) {
        ImmutableList<JavaDLTerm> result = ImmutableSLList.<JavaDLTerm>nil();
        for (JavaDLTerm t : ts) {
            result = result.append(copyVariable(t, postfix, services));
        }
        return result;
    }


    private static JavaDLTerm copyVariable(JavaDLTerm t,
                                     String postfix,
                                     Services services) {
        if (t != null) {
            final TermBuilder tb = services.getTermBuilder();
            JavaDLTerm tWithoutLables = tb.unlabel(t);
            JavaDLTerm result =
                   newVariable(tWithoutLables, tWithoutLables.toString() + postfix, services);
            return tb.label(result, t.getLabels());
        } else {
            return null;
        }
    }


    private static JavaDLTerm newVariable(JavaDLTerm t,
                                    String name,
                                    Services services) {
        if (t == null) {
            return null;
        }

        assert t.op() instanceof ProgramVariable : "Expected a program " +
                                                   "variable.";

        final TermBuilder tb = services.getTermBuilder();
        String newName = tb.newName(name);
        ProgramElementName pen = new ProgramElementName(newName);
        ProgramVariable progVar = (ProgramVariable) t.op();
        LocationVariable newVar = new LocationVariable(pen, progVar.getKeYJavaType(),
                                                       progVar.getContainerType(),
                                                       progVar.isStatic(), progVar.isModel());
        register(newVar, services);
        return tb.var(newVar);
    }


    private static JavaDLTerm copyHeapSymbol(JavaDLTerm t,
                                       String postfix,
                                       Services services) {
        if (t != null) {
            final TermBuilder tb = services.getTermBuilder();
            JavaDLTerm tWithoutLables = tb.unlabel(t);
            JavaDLTerm result =
                   newHeapSymbol(tWithoutLables, tWithoutLables.toString() + postfix, services);
            return tb.label(result, t.getLabels());
        } else {
            return null;
        }
    }


    private static JavaDLTerm newHeapSymbol(JavaDLTerm t,
                                      String name,
                                      Services services) {
        if (t == null) {
            return null;
        }
        if (!(t.op() instanceof Function)) {
            // Sometimes the heap term operator is a location variable (for
            // instance if it is the base heap). Create a location variable
            // in this case.
            return newVariable(t, name, services);
        } else {
            // Otherwise (this is the normal case), the heap term operator is
            // a function (for instance if it is a anon heap). Create a function
            // in this case.
            return newFunction(t, name, services);
        }
    }


    private static JavaDLTerm newFunction(JavaDLTerm t,
                                    String name,
                                    Services services) {
        if (t == null) {
            return null;
        }
        final TermBuilder tb = services.getTermBuilder();
        final Function newFunc = new Function(new Name(name), t.sort());
        register(newFunc, services);
        return tb.func(newFunc);
    }


    private static JavaDLTerm copyFunction(JavaDLTerm t,
                                     String postfix,
                                     Services services) {
        if (t != null) {
            final TermBuilder tb = services.getTermBuilder();
            JavaDLTerm tWithoutLables = tb.unlabel(t);
            JavaDLTerm result =
                   newFunction(tWithoutLables, tWithoutLables.toString() + postfix, services);
            return tb.label(result, t.getLabels());
        } else {
            return null;
        }
    }


    public static StateVars buildMethodContractPreVars(IProgramMethod pm,
                                                       KeYJavaType kjt,
                                                       Services services) {
        ImmutableArray<TermLabel> heapLabels =
                new ImmutableArray<TermLabel>(ParameterlessTermLabel.ANON_HEAP_LABEL);
        return new StateVars(buildSelfVar(services, pm, kjt, ""),
                             buildParamVars(services, "", pm),
                             buildResultVar(pm, services, ""),
                             buildExceptionVar(services, "", pm),
                             buildHeapFunc("AtPre", heapLabels, services),
                             buildMbyVar("", services));
    }


    public static StateVars buildMethodContractPostVars(StateVars preVars,
                                                        IProgramMethod pm,
                                                        KeYJavaType kjt,
                                                        Services services) {
        final String postfix = "AtPost";
        return new StateVars(buildSelfVar(services, pm, kjt, postfix),
                             preVars.localVars, // no local out variables
                             buildResultVar(pm, services, postfix),
                             buildExceptionVar(services, postfix, pm),
                             buildHeapFunc(postfix,
                                           new ImmutableArray<TermLabel>(),
                                           services),
                             preVars.mbyAtPre);
    }


    public static StateVars buildInfFlowPreVars(StateVars origPreVars,
                                                String postfix,
                                                Services services) {
        return new StateVars(origPreVars, postfix, services);
    }


    public static StateVars buildInfFlowPostVars(StateVars origPreVars,
                                                 StateVars origPostVars,
                                                 StateVars preVars,
                                                 String postfix,
                                                 Services services) {
        // create new post vars if original pre and original post var differ;
        // else use pre var
        JavaDLTerm self = (origPreVars.self == origPostVars.self) ?
                    preVars.self :
                    copyVariable(origPostVars.self, postfix, services);
        JavaDLTerm guard = (origPreVars.guard == origPostVars.guard) ?
                     preVars.guard :
                     copyVariable(origPostVars.guard, postfix, services);
        JavaDLTerm result = (origPreVars.result == origPostVars.result) ?
                    preVars.result :
                    copyVariable(origPostVars.result, postfix, services);
        JavaDLTerm exception = (origPreVars.exception == origPostVars.exception) ?
                    preVars.exception :
                    copyVariable(origPostVars.exception, postfix, services);
        JavaDLTerm heap = (origPreVars.heap == origPostVars.heap) ?
                    preVars.heap :
                    copyHeapSymbol(origPostVars.heap, postfix, services);
        JavaDLTerm mbyAtPre = (origPreVars.mbyAtPre == origPostVars.mbyAtPre) ?
                    preVars.mbyAtPre :
                    copyVariable(origPostVars.mbyAtPre, postfix, services);

        ImmutableList<JavaDLTerm> localPostVars = ImmutableSLList.<JavaDLTerm>nil();
        Iterator<JavaDLTerm> origPreVarsIt = origPreVars.localVars.iterator();
        Iterator<JavaDLTerm> localPreVarsIt = preVars.localVars.iterator();
        for (JavaDLTerm origPostVar : origPostVars.localVars) {
            JavaDLTerm origPreVar = origPreVarsIt.next();
            JavaDLTerm localPreVar = localPreVarsIt.next();
            JavaDLTerm localPostVar = (origPreVar == origPostVar) ?
                    localPreVar :
                    copyVariable(origPostVar, postfix, services);
            localPostVars = localPostVars.append(localPostVar);
        }
        return new StateVars(self,
                             guard,
                             localPostVars,
                             result,
                             exception,
                             heap,
                             mbyAtPre);
    }


    private static JavaDLTerm buildSelfVar(Services services,
                                     IProgramMethod pm,
                                     KeYJavaType kjt,
                                     String postfix) {
        if (pm.isStatic()) {
            return null;
        }
        final TermBuilder tb = services.getTermBuilder();
        JavaDLTerm selfVar = tb.var(tb.selfVar(pm, kjt, true, postfix));
        register(selfVar.op(ProgramVariable.class), services);
        return selfVar;
    }


    private static ImmutableList<JavaDLTerm> buildParamVars(Services services,
                                                      String postfix,
                                                      IProgramMethod pm) {
        final TermBuilder tb = services.getTermBuilder();
        ImmutableList<JavaDLTerm> paramVars =
                tb.var(tb.paramVars(postfix, pm, true));
        register(ops(paramVars, ProgramVariable.class), services);
        return paramVars;
    }


    private static JavaDLTerm buildResultVar(IProgramMethod pm,
                                       Services services,
                                       String postfix) {
        if (pm.isVoid() || pm.isConstructor()) {
            return null;
        }
        final TermBuilder tb = services.getTermBuilder();
        JavaDLTerm resultVar =
                tb.var(tb.resultVar("result" + postfix, pm, true));
        register(resultVar.op(ProgramVariable.class), services);
        return resultVar;
    }


    private static JavaDLTerm buildHeapFunc(String postfix,
                                      ImmutableArray<TermLabel> labels,
                                      Services services) {
        HeapLDT heapLDT = services.getTheories().getHeapLDT();
        final TermBuilder tb = services.getTermBuilder();
        if ("".equals(postfix)) {
            return tb.getBaseHeap();
        } else {
            Name heapName = new Name("heap" + postfix);
            Function heap =
                     new Function(heapName, heapLDT.getHeap().sort());
            JavaDLTerm heapFunc = tb.func(heap);
            register(heap, services);
            return tb.label(heapFunc, labels);
        }
    }


    private static JavaDLTerm buildExceptionVar(Services services,
                                          String postfix,
                                          IProgramMethod pm) {
        final TermBuilder tb = services.getTermBuilder();
        JavaDLTerm excVar = tb.var(tb.excVar("exc" + postfix, pm, true));
        register(excVar.op(ProgramVariable.class), services);
        return excVar;
    }


    private static JavaDLTerm buildMbyVar(String postfix,
                                    Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Sort intSort =
                services.getTheories().getIntegerLDT().targetSort();
        String newName = tb.newName("mbyAtPre" + postfix);
        final Function mbyAtPreFunc =
                new Function(new Name(newName), intSort);
        register(mbyAtPreFunc, services);
        return tb.func(mbyAtPreFunc);
    }


    static void register(ProgramVariable pv,
                         Services services) {
        Namespace progVarNames = services.getNamespaces().programVariables();
        if (pv != null && progVarNames.lookup(pv.name()) == null) {
            progVarNames.addSafely(pv);
        }
    }


    static void register(ImmutableList<ProgramVariable> pvs,
                         Services services) {
        for (ProgramVariable pv : pvs) {
            register(pv, services);
        }
    }


    static void register(Function f,
                         Services services) {
        Namespace functionNames = services.getNamespaces().functions();
        if (f != null && functionNames.lookup(f.name()) == null) {
            assert f.sort() != Sort.UPDATE;
            if (f.sort() == Sort.FORMULA) {
                functionNames.addSafely(f);
            } else {
                functionNames.addSafely(f);
            }
        }
    }


    static <T> ImmutableList<T> ops(ImmutableList<JavaDLTerm> terms,
                                    Class<T> opClass)
            throws IllegalArgumentException {
        ImmutableList<T> ops = ImmutableSLList.<T>nil();
        for (JavaDLTerm t : terms) {
            ops = ops.append(t.op(opClass));
        }
        return ops;
    }


    @Override
    public String toString() {
        return termList.toString();
    }
}