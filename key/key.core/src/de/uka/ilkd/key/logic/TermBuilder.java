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

package de.uka.ilkd.key.logic;


import java.io.StringReader;
import java.util.*;

import org.key_project.common.core.logic.CCTermBuilder;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Namespace;
import org.key_project.common.core.logic.NamespaceSet;
import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.*;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TheoryServices;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;


/**
 * <p>Use this class if you intend to build complex terms by hand. It is
 * more convenient than the @link{GenericTermFactory} class.</p>
 *
 * <p>Attention: some methods of this class try to simplify some terms. So if you
 * want to be sure that the term looks exactly as you built it, you
 * will have to use the GenericTermFactory.</p>
 */
public class TermBuilder implements CCTermBuilder<JavaBlock, JavaDLTerm> {

    private static final String JAVA_LANG_THROWABLE = "java.lang.Throwable";

    private final TermFactory tf;
    private final JavaDLTerm tt;
    private final JavaDLTerm ff;

    protected final Services services; // TODO; Make private
    protected final TheoryServices theories;
    
    public TermBuilder(TermFactory tf, Services services) {
       this.services = services;
       assert services != null;
       
       this.theories = services.getTheories();
       assert theories != null;
       
       this.tf = tf;
       this.tt = tf.createTerm(Junctor.TRUE);
       this.ff = tf.createTerm(Junctor.FALSE);
    }


    @Override
    public TermFactory tf() {
        return tf;
    }


    //-------------------------------------------------------------------------
    // build terms using the KeY parser
    //-------------------------------------------------------------------------

    /**
     * Parses the given string that represents the term (or createTerm) using the
     * service's namespaces.
     *
     * @param s
     *            the String to parse
     */
//    @Override
    public JavaDLTerm parseTerm(String s) throws ParserException {
        return parseTerm(s, services.getNamespaces());
    }

    /**
     * Parses the given string that represents the term (or createTerm) using the
     * provided namespaces.
     *
     * @param s
     *            the String to parse
     * @param namespaces
     *            the namespaces used for name lookup.
     * @throws de.uka.ilkd.key.parser.ParserException
     */
//    @Override
    public JavaDLTerm parseTerm(String s, NamespaceSet namespaces)
        throws ParserException
    {
        AbbrevMap abbr = (services.getProof() == null)
                       ? null : services.getProof().abbreviations();
        JavaDLTerm term = new DefaultTermParser().parse(
           new StringReader(s), null, services, namespaces, abbr);
        return term;
    }

    //-------------------------------------------------------------------------
    //naming
    //-------------------------------------------------------------------------

    @Override
    public String shortBaseName(Sort s) {
    String result = s.name().toString();
    int index = result.lastIndexOf(".");
    if(index == -1) {
        result = result.charAt(0) + "";
    } else {
        result = result.substring(index).charAt(1) + "";
    }
    return result.toLowerCase();
    }

    /**
     * Returns an available name constructed by affixing a counter to the passed
     * base name.
     */
    @Override
    public String newName(String baseName) {
        final Name savedName = services.getNameRecorder().getProposal();
        if (savedName != null) {
            // CS: bugfix -- saving name proposals.
            // getProposal() removes the name proposal form the name recorder,
            // but we need to have it again for saving. Therefore I appended
            // the proposal at the and of the list again.
            services.getNameRecorder().addProposal(savedName);

            return savedName.toString();
        }

        final NamespaceSet namespaces = services.getNamespaces();

        int i = 0;
        String result = baseName;
        while (namespaces.lookup(new Name(result)) != null) {
            result = baseName + "_" + i++;
        }

        services.getNameRecorder().addProposal(new Name(result));

        return result;
    }


    /**
     * Returns an available name constructed by affixing a counter to a self-
     * chosen base name for the passed sort.
     */
    @Override
    public String newName(Sort sort) {
        return newName(shortBaseName(sort));
    }




    //-------------------------------------------------------------------------
    //common variable constructions
    //-------------------------------------------------------------------------

    /**
     * Creates a program variable for "self". Take care to register it
     * in the namespaces!
     */
//    @Override
    public LocationVariable selfVar(KeYJavaType kjt,
                                    boolean makeNameUnique) {
        return selfVar(kjt, makeNameUnique, "");
    }


    /**
     * Creates a program variable for "self". Take care to register it
     * in the namespaces!
     */
//    @Override
    public LocationVariable selfVar(KeYJavaType kjt,
                                    boolean makeNameUnique,
                                    String postfix) {
        String name = "self" + postfix;
        if(makeNameUnique) {
            name = newName(name);
        }
        return new LocationVariable(new ProgramElementName(name), kjt);
    }


    /**
     * Creates a program variable for "self". Take care to register it
     * in the namespaces!
     */
//    @Override
    public LocationVariable selfVar(IProgramMethod pm,
                                    KeYJavaType kjt,
                                    boolean makeNameUnique,
                                    String postfix) {
        if(pm.isStatic()) {
            return null;
        } else {
            return selfVar(kjt, makeNameUnique, postfix);
        }
    }

    /**
     * Creates a program variable for "self". Take care to register it
     * in the namespaces!
     */
//    @Override
    public LocationVariable selfVar(IProgramMethod pm,
                                    KeYJavaType kjt,
                                    boolean makeNameUnique) {
        if(pm.isStatic()) {
            return null;
        } else {
            return selfVar(kjt, makeNameUnique);
        }
    }


    /**
     * Creates program variables for the parameters. Take care to register them
     * in the namespaces!
     */
//    @Override
    public ImmutableList<ProgramVariable> paramVars(IObserverFunction obs,
                                                    boolean makeNamesUnique) {
        ImmutableList<ProgramVariable> result
            = ImmutableSLList.<ProgramVariable>nil();
        for(int i = 0, n = obs.getNumParams(); i < n; i++) {
            final KeYJavaType paramType = obs.getParamType(i);
            String name;
            if(obs instanceof IProgramMethod) {
            name = ((IProgramMethod)obs).getParameterDeclarationAt(i)
                                       .getVariableSpecification()
                                       .getName();
            } else {
            name = paramType.getSort().name().toString().charAt(0) + "";
            }
            if(makeNamesUnique) {
            name = newName(name);
            }
            final LocationVariable paramVar
                = new LocationVariable(new ProgramElementName(name), paramType);
            result = result.append(paramVar);
        }
        return result;
    }


    /**
     * Creates program variables for the parameters. Take care to register them
     * in the namespaces!
     */
//    @Override
    public ImmutableList<ProgramVariable> paramVars(String postfix,
        IObserverFunction obs, boolean makeNamesUnique) {
    final ImmutableList<ProgramVariable> paramVars
        = paramVars(obs, true);
    ImmutableList<ProgramVariable> result
            = ImmutableSLList.<ProgramVariable>nil();
        for(ProgramVariable paramVar : paramVars) {
            ProgramElementName pen
                = new ProgramElementName(paramVar.name() + postfix);
            LocationVariable formalParamVar
                = new LocationVariable(pen, paramVar.getKeYJavaType());
            result = result.append(formalParamVar);
        }
        return result;
    }


    /**
     * Creates a program variable for the result. Take care to register it
     * in the namespaces.
     */
//    @Override
    public LocationVariable resultVar(IProgramMethod pm,
                                      boolean makeNameUnique) {
    return resultVar("result", pm, makeNameUnique);
    }


    /**
     * Creates a program variable for the result with passed name. Take care to
     * register it in the namespaces.
     */
//    @Override
    public LocationVariable resultVar(String name, IProgramMethod pm,
        boolean makeNameUnique) {
    if(pm.isVoid() || pm.isConstructor()) {
        return null;
    } else {
        if(makeNameUnique) {
        name = newName(name);
        }
        return new LocationVariable(new ProgramElementName(name),
                        pm.getReturnType());
    }
    }


    /**
     * Creates a program variable for the thrown exception. Take care to
     * register it in the namespaces.
     */
//    @Override
    public LocationVariable excVar(IProgramMethod pm,
                                   boolean makeNameUnique) {
    return excVar("exc", pm, makeNameUnique);
    }


    /**
     * Creates a program variable for the thrown exception. Take care to
     * register it in the namespaces.
     */
//    @Override
    public LocationVariable excVar(String name,
                       IProgramMethod pm,
                                   boolean makeNameUnique) {
    if(makeNameUnique) {
        name = newName(name);
    }
        return new LocationVariable(new ProgramElementName(name),
                                    services.getProgramServices().getJavaInfo().getTypeByClassName(JAVA_LANG_THROWABLE));
    }


    /**
     * Creates a program variable for the atPre heap. Take care to register it
     * in the namespaces.
     */
//    @Override
    public LocationVariable heapAtPreVar(String baseName,
                                         boolean makeNameUnique) {
        HeapLDT heapLDT = theories.getHeapLDT();
        return heapAtPreVar(baseName, heapLDT.getHeap().sort(), makeNameUnique);
    }

    /**
     * Creates a program variable for the atPre heap. Take care to register it
     * in the namespaces.
     */
//    @Override
    public LocationVariable heapAtPreVar(String baseName,
                                         Sort sort,
                                         boolean makeNameUnique) {
        assert sort != null;
        if(makeNameUnique) {
            baseName = newName(baseName);
        }
        return new LocationVariable(new ProgramElementName(baseName),
                                    new KeYJavaType(sort));
    }


    //-------------------------------------------------------------------------
    //constructors for special classes of term operators
    //-------------------------------------------------------------------------

    @Override
    public JavaDLTerm var(LogicVariable v) {
        return tf.createTerm(v);
    }


//    @Override
    public JavaDLTerm var(ProgramVariable v) {
//  if(v.isMember()) {
//      throw new TermCreationException(
//          "Cannot create term for \"member\" "
//          + "program variable \"" + v + "\". Use field symbols "
//          + "like your mother told you!");
//  }
        return tf.createTerm(v);
    }


//    @Override
    public ImmutableList<JavaDLTerm> var(ProgramVariable ... vs) {
        ImmutableList<JavaDLTerm> result = ImmutableSLList.<JavaDLTerm>nil();
        for (ProgramVariable v : vs) {
            result = result.append(var(v));
        }
        return result;
    }


//    @Override
    public ImmutableList<JavaDLTerm> var(Iterable<ProgramVariable> vs) {
    ImmutableList<JavaDLTerm> result = ImmutableSLList.<JavaDLTerm>nil();
    for (ProgramVariable v : vs) {
        result = result.append(var(v));
    }
        return result;
    }


    @Override
    public JavaDLTerm var(SchemaVariable v) {
    return tf.createTerm(v);
    }


    @Override
    public JavaDLTerm var(ParsableVariable v) {
    return tf.createTerm(v);
    }


    @Override
    public JavaDLTerm func(Function f) {
        return tf.createTerm(f);
    }


    @Override
    public JavaDLTerm func(Function f, JavaDLTerm s) {
        return tf.createTerm(f, s);
    }


    @Override
    public JavaDLTerm func(Function f, JavaDLTerm s1, JavaDLTerm s2) {
        return tf.createTerm(f, s1, s2);
    }


    @Override
    public JavaDLTerm func(Function f, JavaDLTerm ... s) {
        return tf.createTerm(f, s, null, null);
    }

//    @Override
    public JavaDLTerm func(IObserverFunction f, JavaDLTerm ... s) {
       return tf.createTerm(f, s, null, null);
   }

    @Override
    public JavaDLTerm func(Function f,
                 JavaDLTerm[] s,
                 ImmutableArray<QuantifiableVariable> boundVars) {
        return tf.createTerm(f, s, boundVars, null);
    }


//    @Override
    public JavaDLTerm prog(Modality mod, JavaBlock jb, JavaDLTerm t) {
    return tf.createTerm(mod, new JavaDLTerm[]{t}, null, jb);
    }


//    @Override
    public JavaDLTerm prog(Modality mod, JavaBlock jb, JavaDLTerm t, ImmutableArray<TermLabel> labels) {
    return tf.createTerm(mod, new JavaDLTerm[]{t}, null, jb, labels);
    }


    @Override
    public JavaDLTerm box(JavaBlock jb, JavaDLTerm t) {
        return prog(Modality.BOX, jb, t);
    }


    @Override
    public JavaDLTerm dia(JavaBlock jb, JavaDLTerm t) {
        return prog(Modality.DIA, jb, t);
    }


    @Override
    public JavaDLTerm ife(JavaDLTerm cond, JavaDLTerm _then, JavaDLTerm _else) {
        return tf.createTerm(IfThenElse.IF_THEN_ELSE,
                         new JavaDLTerm[]{cond, _then, _else});
    }

    /** Construct a term with the \ifEx operator. */
    @Override
    public JavaDLTerm ifEx(QuantifiableVariable qv, JavaDLTerm cond, JavaDLTerm _then, JavaDLTerm _else) {
        return tf.createTerm(IfExThenElse.IF_EX_THEN_ELSE,
                            new ImmutableArray<JavaDLTerm>(cond,_then,_else),
                            new ImmutableArray<QuantifiableVariable>(qv),
                            null);
    }

    /** Construct a term with the \ifEx operator. */
    @Override
    public JavaDLTerm ifEx(ImmutableList<QuantifiableVariable> qvs, JavaDLTerm cond, JavaDLTerm _then, JavaDLTerm _else) {
        if (qvs.isEmpty()) throw new TermCreationException("no quantifiable variables in ifEx term");
        if (qvs.size()==1) {
            return ifEx(qvs.head(), cond, _then, _else);
        } else {
            return ifEx(qvs.head(), tt(), ifEx(qvs.tail(), cond, _then, _else), _else);
        }
    }

    @Override
    public JavaDLTerm cast(Sort s, JavaDLTerm t) {
    return tf.createTerm(s.getCastSymbol(services), t);
    }


    @Override
    public JavaDLTerm tt() {
        return tt;
    }


    @Override
    public JavaDLTerm ff() {
        return ff;
    }


    @Override
    public JavaDLTerm all(QuantifiableVariable qv, JavaDLTerm t) {
        return tf.createTerm(Quantifier.ALL,
                             new ImmutableArray<JavaDLTerm>(t),
                             new ImmutableArray<QuantifiableVariable>(qv),
                             null);
    }


    @Override
    public JavaDLTerm all(Iterable<QuantifiableVariable> qvs, JavaDLTerm t) {
        JavaDLTerm result = t;
        for (QuantifiableVariable fv : qvs) {
            result = all(fv, result);
        }
        return result;
    }


    @Override
    public JavaDLTerm allClose(JavaDLTerm t) {
    return all(t.freeVars(), t);
    }

    /**
     * Removes universal quantifiers from a formula.
     */
    @Override
    public JavaDLTerm open(JavaDLTerm formula) {
    assert formula.sort() == Sort.FORMULA;
    if(formula.op() == Quantifier.ALL) {
        return open(formula.sub(0));
    } else {
        return formula;
    }
    }


    @Override
    public JavaDLTerm ex(QuantifiableVariable qv, JavaDLTerm t) {
    return tf.createTerm(Quantifier.EX,
                 new ImmutableArray<JavaDLTerm>(t),
                 new ImmutableArray<QuantifiableVariable>(qv),
                 null);
    }


    @Override
    public JavaDLTerm ex(Iterable<QuantifiableVariable> qvs, JavaDLTerm t) {
        JavaDLTerm result = t;
        for (QuantifiableVariable fv : qvs) {
            result = ex(fv, result);
        }
        return result;
    }


    @Override
    public JavaDLTerm bsum(QuantifiableVariable qv,
                     JavaDLTerm a,
                     JavaDLTerm b,
                     JavaDLTerm t) {
        Function bsum = theories.getIntegerLDT().getBsum();
        return func(bsum,
                    new JavaDLTerm[]{a, b, t},
                    new ImmutableArray<QuantifiableVariable>(qv));
    }

    /** General (unbounded) sum */
    @Override
    public JavaDLTerm sum (ImmutableList<QuantifiableVariable> qvs, JavaDLTerm range, JavaDLTerm t) {
        final Function sum = (Function)services.getNamespaces().functions().lookup("sum");
        final Iterator<QuantifiableVariable> it = qvs.iterator();
        JavaDLTerm res = func(sum, new JavaDLTerm[]{convertToBoolean(range), t}, new ImmutableArray<QuantifiableVariable>(it.next()));
        while (it.hasNext()) {
            res = func(sum, new JavaDLTerm[]{TRUE(), res}, new ImmutableArray<QuantifiableVariable>(it.next()));
        }
        return res;
    }


    /** Constructs a bounded product comprehension expression. */
    @Override
    public JavaDLTerm bprod(QuantifiableVariable qv,
                     JavaDLTerm a,
                     JavaDLTerm b,
                     JavaDLTerm t,
                     TermServices services) {
        Function bprod = theories.getIntegerLDT().getBprod();
        return func(bprod,
                    new JavaDLTerm[]{a, b, t},
                    new ImmutableArray<QuantifiableVariable>(qv));
    }


    /** General (unbounded) product */
    @Override
    public JavaDLTerm prod(
            ImmutableList<QuantifiableVariable> qvs,
            JavaDLTerm range,
            JavaDLTerm t,
            TermServices services) {
        final Function prod =
                (Function) services.getNamespaces().functions().lookup("prod");
        final Iterator<QuantifiableVariable> it = qvs.iterator();
        JavaDLTerm res =
                func(prod, new JavaDLTerm[] { convertToBoolean(range), t },
                        new ImmutableArray<QuantifiableVariable>(it.next()));
        while (it.hasNext()) {
            res =
                    func(prod, new JavaDLTerm[] { TRUE(), res },
                            new ImmutableArray<QuantifiableVariable>(it.next()));
        }
        return res;
    }


    /** minimum operator */
    @Override
    public JavaDLTerm min(
            ImmutableList<QuantifiableVariable> qvs,
            JavaDLTerm range,
            JavaDLTerm t,
            TermServices services) {
        final Function min =
                (Function) services.getNamespaces().functions().lookup("min");
        final Iterator<QuantifiableVariable> it = qvs.iterator();
        JavaDLTerm res =
                func(min, new JavaDLTerm[] { convertToBoolean(range), t },
                        new ImmutableArray<QuantifiableVariable>(it.next()));
        while (it.hasNext()) {
            res =
                    func(min, new JavaDLTerm[] { TRUE(), res },
                            new ImmutableArray<QuantifiableVariable>(it.next()));
        }
        return res;
    }


    /** minimum operator */
    @Override
    public JavaDLTerm max(
            ImmutableList<QuantifiableVariable> qvs,
            JavaDLTerm range,
            JavaDLTerm t,
            TermServices services) {
        final Function max =
                (Function) services.getNamespaces().functions().lookup("max");
        final Iterator<QuantifiableVariable> it = qvs.iterator();
        JavaDLTerm res =
                func(max, new JavaDLTerm[] { convertToBoolean(range), t },
                        new ImmutableArray<QuantifiableVariable>(it.next()));
        while (it.hasNext()) {
            res =
                    func(max, new JavaDLTerm[] { TRUE(), res },
                            new ImmutableArray<QuantifiableVariable>(it.next()));
        }
        return res;
    }


    @Override
    public JavaDLTerm not(JavaDLTerm t) {
        if(t.op() == Junctor.TRUE) {
            return ff();
        } else if(t.op() == Junctor.FALSE) {
            return tt();
        } else if(t.op() == Junctor.NOT) {
            return t.sub(0);
        } else {
            return tf.createTerm(Junctor.NOT, t);
        }
    }


    @Override
    public JavaDLTerm and(JavaDLTerm t1, JavaDLTerm t2) {
        if(t1.op() == Junctor.FALSE || t2.op() == Junctor.FALSE) {
            return ff();
        } else if(t1.op() == Junctor.TRUE) {
            return t2;
        } else if(t2.op() == Junctor.TRUE) {
            return t1;
        } else {
            return tf.createTerm(Junctor.AND, t1, t2);
        }
    }

    @Override
    public JavaDLTerm andSC(JavaDLTerm t1, JavaDLTerm t2) {
        if(t1.op() == Junctor.TRUE || t1.op() == Junctor.FALSE
                || t2.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
            return and(t1, t2);
        } else {
            return shortcut(and(t1, t2));
        }
    }

    @Override
    public JavaDLTerm and(JavaDLTerm ... subTerms) {
        JavaDLTerm result = tt();
        for(JavaDLTerm sub : subTerms) {
            result = and(result, sub);
        }
        return result;
    }

    @Override
    public JavaDLTerm andSC(JavaDLTerm ... subTerms) {
        JavaDLTerm result = tt();
        if (subTerms.length == 1) {
            return and(subTerms);
        }
        for(JavaDLTerm sub : subTerms) {
            result = andSC(result, sub);
        }
        return result;
    }

    @Override
    public JavaDLTerm and(Iterable<JavaDLTerm> subTerms) {
        JavaDLTerm result = tt();
        for(JavaDLTerm sub : subTerms) {
            result = and(result, sub);
        }
        return result;
    }

    @Override
    public JavaDLTerm andSC(Iterable<JavaDLTerm> subTerms) {
        JavaDLTerm result = tt();
        int i = 0;
        for(JavaDLTerm sub : subTerms) {
            result = andSC(result, sub);
            i++;
        }
        if (i == 1) {
            return and(subTerms);
        }
        return result;
    }

    @Override
    public JavaDLTerm or(JavaDLTerm t1, JavaDLTerm t2) {
        if(t1.op() == Junctor.TRUE || t2.op() == Junctor.TRUE) {
            return tt();
        } else if(t1.op() == Junctor.FALSE) {
            return t2;
        } else if(t2.op() == Junctor.FALSE) {
            return t1;
        } else {
            return tf.createTerm(Junctor.OR, t1, t2);
        }
    }

    @Override
    public JavaDLTerm orSC(JavaDLTerm t1, JavaDLTerm t2) {
        if(t1.op() == Junctor.TRUE || t1.op() == Junctor.FALSE
                || t2.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
            return or(t1, t2);
        } else {
            return shortcut(or(t1, t2));
        }
    }

    @Override
    public JavaDLTerm or(JavaDLTerm... subTerms) {
        JavaDLTerm result = ff();
        for(JavaDLTerm sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }

    @Override
    public JavaDLTerm orSC(JavaDLTerm... subTerms) {
        JavaDLTerm result = ff();
        if (subTerms.length == 1) {
            return or(subTerms);
        }
        for(JavaDLTerm sub : subTerms) {
            result = orSC(result, sub);
        }
        return result;
    }

    @Override
    public JavaDLTerm or(Iterable<JavaDLTerm> subTerms) {
        JavaDLTerm result = ff();
        for(JavaDLTerm sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }

    @Override
    public JavaDLTerm orSC(Iterable<JavaDLTerm> subTerms) {
        JavaDLTerm result = ff();
        int i = 0;
        for(JavaDLTerm sub : subTerms) {
            result = orSC(result, sub);
            i++;
        }
        if (i == 1) {
            return or(subTerms);
        }
        return result;
    }

    @Override
    public JavaDLTerm imp(JavaDLTerm t1, JavaDLTerm t2) {
        return imp(t1, t2, null);
    }


    @Override
    public JavaDLTerm imp(JavaDLTerm t1, JavaDLTerm t2, ImmutableArray<TermLabel> labels) {
        if(t1.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
            return tt();
        } else if(t1.op() == Junctor.TRUE) {
            return t2;
        } else if(t2.op() == Junctor.FALSE) {
            return not(t1);
        } else {
            return tf.createTerm(Junctor.IMP, t1, t2, labels);
        }
    }


    /**
     * Creates a term with the correct equality symbol for
     * the sorts involved
     */
    @Override
    public JavaDLTerm equals(JavaDLTerm t1, JavaDLTerm t2) {
        if(t1.sort() == Sort.FORMULA) {
            if(t1.op() == Junctor.TRUE) {
                return t2;
            } else if(t2.op() == Junctor.TRUE) {
                return t1;
            } else if(t1.op() == Junctor.FALSE) {
                return not(t2);
            } else if(t2.op() == Junctor.FALSE) {
                return not(t1);
            } else {
                return tf.createTerm(Equality.EQV, t1, t2);
            }
        } else {
            return tf.createTerm(Equality.EQUALS, t1, t2);
        }
    }


    /**
     * Creates a substitution term
     * @param substVar the QuantifiableVariable to be substituted
     * @param substTerm the JavaDLTerm that replaces substVar
     * @param origTerm the JavaDLTerm that is substituted
     */
//    @Override
    public JavaDLTerm subst(SubstOp op,
                      QuantifiableVariable substVar,
                      JavaDLTerm substTerm,
                      JavaDLTerm origTerm) {
        return tf.createTerm(op,
                             new ImmutableArray<JavaDLTerm>(new JavaDLTerm[]{substTerm, origTerm}),
                             new ImmutableArray<QuantifiableVariable>(substVar),
                             null);
    }

    @Override
    public JavaDLTerm subst(QuantifiableVariable substVar,
                  JavaDLTerm substTerm,
                  JavaDLTerm origTerm) {
        return subst(WarySubstOp.SUBST,
                     substVar,
                     substTerm,
                     origTerm);
    }


    @Override
    public JavaDLTerm instance(Sort s, JavaDLTerm t) {
    return equals(func(s.getInstanceofSymbol(services), t),
              TRUE());
    }


    @Override
    public JavaDLTerm exactInstance(Sort s, JavaDLTerm t) {
    return equals(func(s.getExactInstanceofSymbol(services), t),
              TRUE());
    }

    // Functions for wellfoundedness
    //------------------------------

    @Override
    public JavaDLTerm pair(JavaDLTerm first, JavaDLTerm second) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function)funcNS.lookup(new Name("pair"));
        if (f == null)
            throw new RuntimeException("LDT: Function pair not found.\n" +
                    "It seems that there are definitions missing from the .key files.");

        return func(f, first, second);

    }

    @Override
    public JavaDLTerm prec(JavaDLTerm mby, JavaDLTerm mbyAtPre) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function)funcNS.lookup(new Name("prec"));
        if (f == null)
                throw new RuntimeException("LDT: Function prec not found.\n" +
                                "It seems that there are definitions missing from the .key files.");

        return func(f, mby, mbyAtPre);
    }

    @Override
    public JavaDLTerm measuredByCheck(JavaDLTerm mby) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function)funcNS.lookup(new Name("measuredByCheck"));
        if (f == null)
                throw new RuntimeException("LDT: Function measuredByCheck not found.\n" +
                                "It seems that there are definitions missing from the .key files.");
        return func(f, mby);
    }

    @Override
    public JavaDLTerm measuredBy(JavaDLTerm mby) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function)funcNS.lookup(new Name("measuredBy"));
        if (f == null)
                throw new RuntimeException("LDT: Function measuredBy not found.\n" +
                                "It seems that there are definitions missing from the .key files.");
        return func(f, mby);
    }
    @Override
    public Function getMeasuredByEmpty(){
       final Namespace funcNS = services.getNamespaces().functions();
       final Function f = (Function)funcNS.lookup(new Name("measuredByEmpty"));
       if (f == null)
               throw new RuntimeException("LDT: Function measuredByEmpty not found.\n" +
                               "It seems that there are definitions missing from the .key files.");
       return f;
    }
    @Override
    public JavaDLTerm measuredByEmpty() {
        return func(getMeasuredByEmpty());
    }

    /**
     * If a is a boolean literal, the method returns the literal as a Formula.
     */
    @Override
    public JavaDLTerm convertToFormula(JavaDLTerm a) {
        BooleanLDT booleanLDT = theories.getBooleanLDT();
        if (a.sort() == Sort.FORMULA) {
            return a;
        } else if (a.sort() == booleanLDT.targetSort()) {
            // special case where a is the result of convertToBoolean
            if (a.op() == IfThenElse.IF_THEN_ELSE) {
                assert a.arity() == 3;
                assert a.sub(0).sort() == Sort.FORMULA;
                if (a.sub(1).op() == booleanLDT.getTrueConst() && a.sub(2).op() == booleanLDT.getFalseConst())
                    return a.sub(0);
                else if (a.sub(1).op() == booleanLDT.getFalseConst() && a.sub(2).op() == booleanLDT.getTrueConst())
                    return not(a.sub(0));
            }
            return equals(a, TRUE());
        } else {
            throw new TermCreationException("JavaDLTerm " + a + " cannot be converted"
                                            + " into a formula.");
        }
    }

    /** For a formula a, convert it to a boolean expression. */
    @Override
    public JavaDLTerm convertToBoolean(JavaDLTerm a){
        BooleanLDT booleanLDT = theories.getBooleanLDT();
        if (a.sort() == booleanLDT.targetSort()) {
            return a;
        } else if (a.sort() == Sort.FORMULA) {
            // special case where a is the result of convertToFormula
            if (a.op() == Equality.EQUALS && a.sub(1).op() == booleanLDT.getTrueConst() ) {
                return a.sub(0);
            }
            return ife(a, TRUE(), FALSE());
        } else {
            throw new TermCreationException("JavaDLTerm " + a + " cannot be converted"
                    + " into a boolean.");
}
    }


    //-------------------------------------------------------------------------
    //updates
    //-------------------------------------------------------------------------

    @Override
    public JavaDLTerm elementary(UpdateableOperator lhs, JavaDLTerm rhs) {
    ElementaryUpdate eu = ElementaryUpdate.getInstance(lhs);
    return tf.createTerm(eu, rhs);
    }


    @Override
    public JavaDLTerm elementary(JavaDLTerm lhs, JavaDLTerm rhs) {
        HeapLDT heapLDT = theories.getHeapLDT();
    if(lhs.op() instanceof UpdateableOperator) {
        assert lhs.arity() == 0 : "uh oh: " + lhs;
        return elementary((UpdateableOperator)lhs.op(), rhs);
    } else if(heapLDT.getSortOfSelect(lhs.op()) != null
          && lhs.sub(0).op().equals(heapLDT.getHeap())) {
        final JavaDLTerm heapTerm   = lhs.sub(0);
        final JavaDLTerm objectTerm = lhs.sub(1);
        final JavaDLTerm fieldTerm  = lhs.sub(2);

        final JavaDLTerm fullRhs = store(heapTerm,
                                   objectTerm,
                               fieldTerm,
                               rhs);
        return elementary(heapLDT.getHeap(), fullRhs);
    } else {
        throw new TermCreationException("Not a legal lhs: " + lhs);
    }
    }


    private JavaDLTerm elementary(JavaDLTerm heapTerm) {
        return elementary(getBaseHeap(), heapTerm);
    }

    @Override
    public JavaDLTerm skip() {
    return tf.createTerm(UpdateJunctor.SKIP);
    }


    @Override
    public JavaDLTerm parallel(JavaDLTerm u1, JavaDLTerm u2) {
    if(u1.sort() != Sort.UPDATE) {
        throw new TermCreationException("Not an update: " + u1);
    } else if(u2.sort() != Sort.UPDATE) {
        throw new TermCreationException("Not an update: " + u2);
    }
    if(u1.op() == UpdateJunctor.SKIP) {
        return u2;
    } else if(u2.op() == UpdateJunctor.SKIP) {
        return u1;
    }
    return tf.createTerm(UpdateJunctor.PARALLEL_UPDATE, u1, u2);
    }


    @Override
    public JavaDLTerm parallel(JavaDLTerm... updates) {
    JavaDLTerm result = skip();
    for(int i = 0; i < updates.length; i++) {
        result = parallel(result, updates[i]);
    }
    return result;
    }


    @Override
    public JavaDLTerm parallel(ImmutableList<JavaDLTerm> updates) {
    return parallel(updates.toArray(new JavaDLTerm[updates.size()]));
    }


    @Override
    public JavaDLTerm parallel(JavaDLTerm[] lhss, JavaDLTerm[] values) {
    if(lhss.length != values.length) {
        throw new TermCreationException(
            "Tried to create parallel update with "
            + lhss.length + " locs and " + values.length + " values");
    }
    JavaDLTerm[] updates = new JavaDLTerm[lhss.length];
    for(int i = 0; i < updates.length; i++) {
        updates[i] = elementary(lhss[i], values[i]);
    }
    return parallel(updates);
    }


    @Override
    public JavaDLTerm parallel(Iterable<JavaDLTerm> lhss,
                         Iterable<JavaDLTerm> values) {
        ImmutableList<JavaDLTerm> updates = ImmutableSLList.<JavaDLTerm>nil();
        Iterator<JavaDLTerm> lhssIt = lhss.iterator();
        Iterator<JavaDLTerm> rhssIt = values.iterator();
        while (lhssIt.hasNext()) {
            assert rhssIt.hasNext();
            updates = updates.append(elementary(lhssIt.next(), rhssIt.next()));
        }
        return parallel(updates);
    }


    @Override
    public JavaDLTerm sequential(JavaDLTerm u1, JavaDLTerm u2) {
    return parallel(u1, apply(u1, u2, null));
    }


    @Override
    public JavaDLTerm sequential(JavaDLTerm[] updates) {
    if(updates.length == 0) {
        return skip();
    } else {
        JavaDLTerm result = updates[updates.length - 1];
        for(int i = updates.length - 2; i >= 0; i++) {
        result = sequential(updates[i], result);
        }
        return result;
    }
    }


    @Override
    public JavaDLTerm sequential(ImmutableList<JavaDLTerm> updates) {
        if(updates.isEmpty()) {
            return skip();
        } else if(updates.size() == 1) {
            return updates.head();
        } else {
            return sequential(updates.head(), sequential(updates.tail()));
        }
    }

    @Override
    public JavaDLTerm apply(JavaDLTerm update, JavaDLTerm target) {
        return apply(update,target,null);
    }

    @Override
    public ImmutableList<JavaDLTerm> apply(JavaDLTerm update,
            ImmutableList<JavaDLTerm> targets) {
        ImmutableList<JavaDLTerm> result = ImmutableSLList.<JavaDLTerm>nil();
        for (JavaDLTerm target : targets) {
            result = result.append(apply(update, target));
        }
        return result;
    }

    @Override
    public JavaDLTerm apply(JavaDLTerm update, JavaDLTerm target, ImmutableArray<TermLabel> labels) {
        if(update.sort() != Sort.UPDATE) {
            throw new TermCreationException("Not an update: " + update);
        } else if(update.op() == UpdateJunctor.SKIP) {
            return target;
        } else if(target.equals(tt())) {
            return tt();
        } else {
            return tf.createTerm(UpdateApplication.UPDATE_APPLICATION,
                    update,
                    target,
                    labels);
        }
    }


    @Override
    public JavaDLTerm applyElementary(JavaDLTerm loc,
                            JavaDLTerm value,
                            JavaDLTerm target) {
    return apply(elementary(loc, value), target, null);
    }


    @Override
    public JavaDLTerm applyElementary(JavaDLTerm heap,
                            JavaDLTerm target) {
    return apply(elementary(heap), target, null);
    }


    @Override
    public ImmutableList<JavaDLTerm> applyElementary(JavaDLTerm heap,
                            Iterable<JavaDLTerm> targets) {
        ImmutableList<JavaDLTerm> result = ImmutableSLList.<JavaDLTerm>nil();
        for (JavaDLTerm target : targets) {
            result = result.append(apply(elementary(heap), target, null));
        }
    return result;
    }


    @Override
    public JavaDLTerm applyParallel(JavaDLTerm[] updates, JavaDLTerm target) {
    return apply(parallel(updates), target, null);
    }


    @Override
    public JavaDLTerm applyParallel(ImmutableList<JavaDLTerm> updates, JavaDLTerm target) {
    return apply(parallel(updates), target, null);
    }


    @Override
    public JavaDLTerm applyParallel(JavaDLTerm[] lhss,
                          JavaDLTerm[] values,
                          JavaDLTerm target) {
    return apply(parallel(lhss, values), target, null);
    }


    @Override
    public JavaDLTerm applySequential(JavaDLTerm[] updates, JavaDLTerm target) {
    if(updates.length == 0) {
        return target;
    } else {
        ImmutableList<JavaDLTerm> updateList = ImmutableSLList.<JavaDLTerm>nil()
                                            .append(updates)
                                            .tail();
        return apply(updates[0],
                 applySequential(updateList, target), null);
    }
    }


    @Override
    public JavaDLTerm applySequential(ImmutableList<JavaDLTerm> updates, JavaDLTerm target) {
    if(updates.isEmpty()) {
        return target;
    } else {
        return apply(updates.head(),
                 applySequential(updates.tail(), target), null);
    }
    }

//    @Override
    public JavaDLTerm applyUpdatePairsSequential(ImmutableList<UpdateLabelPair> updates, JavaDLTerm target) {
       if(updates.isEmpty()) {
           return target;
       } else {
           return apply(updates.head().getUpdate(),
                 applyUpdatePairsSequential(updates.tail(), target), updates.head().getUpdateApplicationlabels());
       }
       }

    //-------------------------------------------------------------------------
    //boolean operators
    //-------------------------------------------------------------------------

    @Override
    public JavaDLTerm TRUE() {
        return theories.getBooleanLDT().getTrueTerm();
    }


    @Override
    public JavaDLTerm FALSE() {
        return theories.getBooleanLDT().getFalseTerm();
    }



    //-------------------------------------------------------------------------
    //integer operators
    //-------------------------------------------------------------------------

    @Override
    public JavaDLTerm geq(JavaDLTerm t1, JavaDLTerm t2) {
        final IntegerLDT integerLDT = theories.getIntegerLDT();
        return func(integerLDT.getGreaterOrEquals(), t1, t2);
    }


    @Override
    public JavaDLTerm gt(JavaDLTerm t1, JavaDLTerm t2) {
        final IntegerLDT integerLDT = theories.getIntegerLDT();
        return func(integerLDT.getGreaterThan(), t1, t2);
    }


    @Override
    public JavaDLTerm lt(JavaDLTerm t1, JavaDLTerm t2) {
        final IntegerLDT integerLDT = theories.getIntegerLDT();
        return func(integerLDT.getLessThan(), t1, t2);
    }


    @Override
    public JavaDLTerm leq(JavaDLTerm t1, JavaDLTerm t2) {
        final IntegerLDT integerLDT = theories.getIntegerLDT();
        return func(integerLDT.getLessOrEquals(), t1, t2);
    }


    @Override
    public JavaDLTerm zero() {
    return theories.getIntegerLDT().zero();
    }


    @Override
    public JavaDLTerm one() {
        return theories.getIntegerLDT().one();
    }

    /**
     * @param numberString String representing an integer
     * @return JavaDLTerm in Z-Notation representing the given number
     * @throws NumberFormatException if <code>numberString</code> is not a number
     */
    @Override
    public JavaDLTerm zTerm(String numberString) {

        if (numberString == null || numberString.isEmpty()) {
            throw new NumberFormatException(numberString + " is not a number.");
        }

        JavaDLTerm numberLiteralTerm;
        boolean negate = false;
        int j = 0;

        final IntegerLDT intLDT = theories.getIntegerLDT();

        if (numberString.charAt(0) == '-') {
            negate = true;
            j = 1;
        }
        numberLiteralTerm = func(intLDT.getNumberTerminator());

        int digit;
        for (int i = j, sz = numberString.length(); i<sz; i++) {
            switch(numberString.charAt(i)) {
                case '0' : digit = 0; break;
                case '1' : digit = 1; break;
                case '2' : digit = 2; break;
                case '3' : digit = 3; break;
                case '4' : digit = 4; break;
                case '5' : digit = 5; break;
                case '6' : digit = 6; break;
                case '7' : digit = 7; break;
                case '8' : digit = 8; break;
                case '9' : digit = 9; break;
                default:
                    throw new NumberFormatException(numberString + " is not a number.");
            }

            numberLiteralTerm = func(intLDT.getNumberLiteralFor(digit), numberLiteralTerm);
        }
        if (negate) {
            numberLiteralTerm = func(intLDT.getNegativeNumberSign(), numberLiteralTerm);
        }
        numberLiteralTerm = func(intLDT.getNumberSymbol(), numberLiteralTerm);
        return numberLiteralTerm;
    }

    /**
     * @param number an integer
     * @return JavaDLTerm in Z-Notation representing the given number
     */
    @Override
    public JavaDLTerm zTerm(long number) {
        return zTerm(""+number);
    }


    @Override
    public JavaDLTerm add(JavaDLTerm t1, JavaDLTerm t2) {
        final IntegerLDT integerLDT = theories.getIntegerLDT();
        final JavaDLTerm zero = integerLDT.zero();
        if(t1.equals(zero)) {
            return t2;
        } else if(t2.equals(zero)) {
            return t1;
        } else {
            return func(integerLDT.getAdd(), t1, t2);
        }
    }

    @Override
    public JavaDLTerm inByte(JavaDLTerm var) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inByte"));
        return func(f, var);
    }

    @Override
    public JavaDLTerm inShort(JavaDLTerm var) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inShort"));
        return func(f, var);
    }

    @Override
    public JavaDLTerm inChar(JavaDLTerm var) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inChar"));
        return func(f, var);
    }

    @Override
    public JavaDLTerm inInt(JavaDLTerm var) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inInt"));
        return func(f, var);
    }



    @Override
    public JavaDLTerm inLong(JavaDLTerm var) {
        Function f =
                (Function) services.getNamespaces().functions().lookup(
                new Name("inLong"));
        return func(f, var);
    }

    @Override
    public JavaDLTerm index(){
        return func(theories.getIntegerLDT().getIndex());
    }



    //-------------------------------------------------------------------------
    //location set operators
    //-------------------------------------------------------------------------

    /**
     * This value is only used as a marker for "\strictly_nothing" in JML. It
     * may return any term. Preferably of type LocSet, but this is not
     * necessary.
     *
     * @return an arbitrary but fixed term.
     */
    @Override
    public JavaDLTerm strictlyNothing() {
        return ff();
    }

    @Override
    public JavaDLTerm empty() {
    return func(theories.getLocSetLDT().getEmpty());
    }


    @Override
    public JavaDLTerm allLocs() {
    return func(theories.getLocSetLDT().getAllLocs());
    }


    @Override
    public JavaDLTerm singleton(JavaDLTerm o, JavaDLTerm f) {
    return func(theories.getLocSetLDT().getSingleton(),
            o,
            f);
    }


    @Override
    public JavaDLTerm union(JavaDLTerm s1, JavaDLTerm s2) {
        final LocSetLDT ldt = theories.getLocSetLDT();
        if(s1.op() == ldt.getEmpty()) {
            return s2;
        } else if(s2.op() == ldt.getEmpty()) {
            return s1;
        } else {
            return func(ldt.getUnion(), s1, s2);
        }
    }


    @Override
    public JavaDLTerm union(JavaDLTerm ... subTerms) {
        JavaDLTerm result = empty();
        for(JavaDLTerm sub : subTerms) {
        result = union(result, sub);
        }
        return result;
    }


    @Override
    public JavaDLTerm union(Iterable<JavaDLTerm> subTerms) {
        JavaDLTerm result = empty();
        for(JavaDLTerm sub : subTerms) {
        result = union(result, sub);
        }
        return result;
    }


    @Override
    public JavaDLTerm intersect(JavaDLTerm s1, JavaDLTerm s2) {
        final LocSetLDT ldt = theories.getLocSetLDT();
        if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
            return empty();
        } else {
            return func(ldt.getIntersect(), s1, s2);
        }
    }


    @Override
    public JavaDLTerm intersect(JavaDLTerm ... subTerms) {
        JavaDLTerm result = empty();
        for(JavaDLTerm sub : subTerms) {
            result = intersect(result, sub);
        }
        return result;
    }


    @Override
    public JavaDLTerm intersect(Iterable<JavaDLTerm> subTerms) {
        JavaDLTerm result = empty();
        for(JavaDLTerm sub : subTerms) {
            result = intersect(result, sub);
        }
        return result;
    }


    @Override
    public JavaDLTerm setMinus(JavaDLTerm s1, JavaDLTerm s2) {
        final LocSetLDT ldt = theories.getLocSetLDT();
        if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
            return s1;
        } else {
            return func(ldt.getSetMinus(), s1, s2);
        }
    }


    @Override
    public JavaDLTerm infiniteUnion(QuantifiableVariable[] qvs,
                              JavaDLTerm s) {
        final LocSetLDT ldt = theories.getLocSetLDT();
        return tf.createTerm(ldt.getInfiniteUnion(),
                new JavaDLTerm[]{s},
                new ImmutableArray<QuantifiableVariable>(qvs),
                null);
    }


    @Override
    public JavaDLTerm infiniteUnion(QuantifiableVariable[] qvs,
                         JavaDLTerm guard,
                         JavaDLTerm s) {
        return infiniteUnion(qvs,
                             ife(guard, s, empty()));
    }


    @Override
    public JavaDLTerm setComprehension(QuantifiableVariable[] qvs,
                                 JavaDLTerm o,
                                 JavaDLTerm f) {
        return infiniteUnion(qvs, singleton(o, f));
    }


    @Override
    public JavaDLTerm setComprehension(QuantifiableVariable[] qvs,
                                JavaDLTerm guard,
                                JavaDLTerm o,
                                JavaDLTerm f) {
        return infiniteUnion(qvs,
                                    guard,
                                    singleton(o, f));
    }


    @Override
    public JavaDLTerm allFields(JavaDLTerm o) {
        return func(theories.getLocSetLDT().getAllFields(), o);
    }


    @Override
    public JavaDLTerm allObjects(JavaDLTerm f) {
        return func(theories.getLocSetLDT().getAllObjects(), f);
    }


    @Override
    public JavaDLTerm arrayRange(JavaDLTerm o, JavaDLTerm lower, JavaDLTerm upper) {
        return func(theories.getLocSetLDT().getArrayRange(),
                o, lower, upper);
    }


    @Override
    public JavaDLTerm freshLocs(JavaDLTerm h) {
        return func(theories.getLocSetLDT().getFreshLocs(), h);
    }


    @Override
    public JavaDLTerm elementOf(JavaDLTerm o, JavaDLTerm f, JavaDLTerm s) {
        final LocSetLDT ldt = theories.getLocSetLDT();
        if(s.op() == ldt.getEmpty()) {
            return ff();
        } else {
            return func(ldt.getElementOf(), o, f, s);
        }
    }


    @Override
    public JavaDLTerm subset(JavaDLTerm s1, JavaDLTerm s2) {
        final LocSetLDT ldt = theories.getLocSetLDT();
        if(s1.op() == ldt.getEmpty()) {
            return tt();
        } else {
            return func(ldt.getSubset(), s1, s2);
        }
    }


    @Override
    public JavaDLTerm disjoint(JavaDLTerm s1, JavaDLTerm s2) {
        final LocSetLDT ldt = theories.getLocSetLDT();
        if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
            return tt();
        } else {
            return func(ldt.getDisjoint(), s1, s2);
        }
    }


    @Override
    public JavaDLTerm createdInHeap(JavaDLTerm s, JavaDLTerm h) {
        final LocSetLDT ldt = theories.getLocSetLDT();
        if(s.op() == ldt.getEmpty()) {
            return tt();
        } else {
            return func(ldt.getCreatedInHeap(), s, h);
        }
    }


    @Override
    public JavaDLTerm createdLocs() {
        return setMinus(allLocs(),
                    freshLocs(getBaseHeap()));
    }

    // The template of the well-definedness transformer for terms.
    public static final Transformer WD_ANY =
            new Transformer(new Name("wd"), SortImpl.ANY);

    // The template of the well-definedness transformer for formulas.
    public static final Transformer WD_FORMULA =
            new Transformer(new Name("WD"), Sort.FORMULA);

    @Override
    public JavaDLTerm wd(JavaDLTerm t) {
        if(t.op() == Junctor.FALSE || t.op() == Junctor.TRUE) {
            return tt();
        } else if (t.sort().equals(Sort.FORMULA)) {
            return func(Transformer.getTransformer(WD_FORMULA, services), t);
        } else {
            return func(Transformer.getTransformer(WD_ANY, services), t);
        }
    }

    @Override
    public ImmutableList<JavaDLTerm> wd(Iterable<JavaDLTerm> l) {
        ImmutableList<JavaDLTerm> res = ImmutableSLList.<JavaDLTerm>nil();
        for (JavaDLTerm t: l) {
            res = res.append(wd(t));
        }
        return res;
    }

    @Override
    public JavaDLTerm[] wd(JavaDLTerm[] l) {
        JavaDLTerm[] res = new JavaDLTerm[l.length];
        for(int i = 0; i < l.length; i++) {
            res[i] = wd(l[i]);
        }
        return res;
    }


    //-------------------------------------------------------------------------
    //heap operators
    //-------------------------------------------------------------------------

    @Override
    public JavaDLTerm NULL() {
        return func(theories.getHeapLDT().getNull());
    }
    
    /** The "deep non null" predicate arising from JML non_null types.
     * Deep non null means that it is recursively defined for arrays.
     * See bug #1392.
     */
    @Override
    public JavaDLTerm deepNonNull(JavaDLTerm o, JavaDLTerm d) {
        final Function nonNull = (Function) services.getNamespaces().functions().lookup("nonNull");
        final JavaDLTerm heap = getBaseHeap();
        return func(nonNull, heap, o, d);
    }

    @Override
    public JavaDLTerm wellFormed(JavaDLTerm heap) {
        return func(theories.getHeapLDT().getWellFormed(), heap);
    }

//    @Override
    public JavaDLTerm wellFormed(LocationVariable heap) {
        return wellFormed(var(heap));
    }

    @Override
    public JavaDLTerm permissionsFor(JavaDLTerm permHeap, JavaDLTerm regularHeap) {
        return func(theories.getPermissionLDT().getPermissionsFor(),
                permHeap, regularHeap);
    }

//    @Override
    public JavaDLTerm permissionsFor(LocationVariable permHeap, LocationVariable regularHeap) {
        return permissionsFor(var(permHeap),var(regularHeap));
    }

    @Override
    public JavaDLTerm inv(JavaDLTerm[] h, JavaDLTerm o) {
        JavaDLTerm[] p = new JavaDLTerm[h.length + 1];
        System.arraycopy(h, 0, p, 0, h.length);
        p[h.length] = o;
        return func(services.getProgramServices().getJavaInfo().getInv(), p);
    }


    @Override
    public JavaDLTerm inv(JavaDLTerm o) {
        List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        JavaDLTerm[] hs = new JavaDLTerm[heaps.size()];
        int i=0;
        for(LocationVariable heap : heaps) {
            hs[i++] = var(heap);
        }
        return inv(hs, o);
    }

//    @Override
    public JavaDLTerm staticInv(JavaDLTerm[] h, KeYJavaType t){
        return func(services.getProgramServices().getJavaInfo().getStaticInv(t), h);
    }

//    @Override
    public JavaDLTerm staticInv(KeYJavaType t){
        List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        JavaDLTerm[] hs = new JavaDLTerm[heaps.size()];
        int i=0;
        for(LocationVariable heap : heaps) {
            hs[i++] = var(heap);
        }
        return func(services.getProgramServices().getJavaInfo().getStaticInv(t), hs);
    }


    @Override
    public JavaDLTerm select(Sort asSort, JavaDLTerm h, JavaDLTerm o, JavaDLTerm f) {
    return func(theories.getHeapLDT().getSelect(
            asSort,
            services),
            h, o, f);
    }
    
    /**
     * Get the select expression for a location variabe
     * representing the field.
     */
//    @Override
    public JavaDLTerm select(Sort asSort, JavaDLTerm h, JavaDLTerm o, LocationVariable field) {
        final Function f = theories.getHeapLDT().getFieldSymbolForPV(field, services);
        return select(asSort, h, o, func(f));
    }


    @Override
    public JavaDLTerm dot(Sort asSort, JavaDLTerm o, JavaDLTerm f) {
        return select(asSort, getBaseHeap(), o, f);
    }

    @Override
    public JavaDLTerm getBaseHeap() {
        return var(theories.getHeapLDT().getHeap());
    }

    @Override
    public JavaDLTerm dot(Sort asSort, JavaDLTerm o, Function f) {
    final Sort fieldSort
        = theories.getHeapLDT().getFieldSort();
        return f.sort() == fieldSort
               ? dot(asSort, o, func(f))
               : func(f, getBaseHeap(), o);
    }
    
//    @Override
    public JavaDLTerm dot (Sort asSort, JavaDLTerm o, LocationVariable field) {
        final Function f = theories.getHeapLDT().getFieldSymbolForPV(field, services);
        return dot(asSort, o, f);
    }


    @Override
    public JavaDLTerm staticDot(Sort asSort, JavaDLTerm f) {
        return dot(asSort, NULL(), f);
    }


    @Override
    public JavaDLTerm staticDot(Sort asSort, Function f) {
    final Sort fieldSort
        = theories.getHeapLDT().getFieldSort();
    return f.sort() == fieldSort
           ? staticDot(asSort, func(f))
           : func(f, getBaseHeap());
    }


    @Override
    public JavaDLTerm arr(JavaDLTerm idx) {
    return func(theories.getHeapLDT().getArr(), idx);
    }

    @Override
    public JavaDLTerm addLabel(JavaDLTerm term, ImmutableArray<TermLabel> labels) {
        if ((labels == null || labels.isEmpty())
                && !term.hasLabels()) {
            return term;
        } else if (!term.hasLabels()) {
            return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                    term.modalContent(), labels);
        } else {
            ArrayList<TermLabel> newLabelList = new ArrayList<TermLabel>();           
            for (TermLabel l: term.getLabels()) {
                newLabelList.add(l);                
            }
            for (TermLabel l: labels) {
                if (!newLabelList.contains(l)) {
                    newLabelList.add(l);
                }
            }
            return tf.createTerm(term.op(), term.subs(),
                    term.boundVars(), term.modalContent(),
                    new ImmutableArray<TermLabel>(newLabelList));
        }
    }

    @Override
    public JavaDLTerm addLabel(JavaDLTerm term, TermLabel label) {
        if (label == null && !term.hasLabels()) {
            return term;
        } else {
            return addLabel(term, new ImmutableArray<TermLabel>(label));
        }
    }

    @Override
    public JavaDLTerm label(JavaDLTerm term, ImmutableArray<TermLabel> labels) {
        if ((labels == null || labels.isEmpty())) {
            return term;
        } else if (labels.size() == 1
                && (labels.contains(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)
                        || labels.contains(ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL)
                        || labels.contains(ParameterlessTermLabel.UNDEFINED_VALUE_LABEL))
                && !WellDefinednessCheck.isOn()) {
            return term; // FIXME: This case is only for SET Tests
        } else {
            return tf.createTerm(term.op(), term.subs(), term.boundVars(),
                                 term.modalContent(), labels);
        }
    }

    @Override
    public JavaDLTerm label(JavaDLTerm term, TermLabel label) {
        if (label == null) {
            return term;
        } else {
            return label(term, new ImmutableArray<TermLabel>(label));
        }
    }

    @Override
    public JavaDLTerm shortcut(JavaDLTerm term) {
        if ((term.op().equals(Junctor.AND)
                        || term.op().equals(Junctor.OR))
            && WellDefinednessCheck.isOn()) { // FIXME: Last condition is only for SET Tests
            return addLabel(term, ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL);
        } else {
            return term;
        }
    }

    @Override
    public JavaDLTerm unlabel(JavaDLTerm term) {
        return tf.createTerm(term.op(), term.subs(), term.boundVars(), term.modalContent());
    }

    @Override
    public JavaDLTerm unlabelRecursive(JavaDLTerm term) {
        JavaDLTerm[] subs = new JavaDLTerm[term.arity()];
        for (int i = 0; i < subs.length; i++) {
            subs[i] = unlabelRecursive(term.sub(i));
        }
        return tf.createTerm(term.op(), subs, term.boundVars(), term.modalContent());
    }

    @Override
    public JavaDLTerm dotArr(JavaDLTerm ref, JavaDLTerm idx) {
        if(ref == null || idx == null) {
            throw new TermCreationException("Tried to build an array access "+
                    "term without providing an " +
                    (ref==null ? "array reference." : "index.") +
                    "("+ref+"["+idx+"])");
        }

        final Sort elementSort;
        if(ref.sort() instanceof ArraySort) {
            elementSort = ((ArraySort) ref.sort()).elementSort();
        } else {
            throw new TermCreationException("Tried to build an array access "+
                    "on an inacceptable sort: " + ref.sort().getClass() + "\n" +
                    "("+ref+"["+idx+"])");
        }

        return select(elementSort,
                  getBaseHeap(),
                  ref,
                  arr(idx));
    }


    @Override
    public JavaDLTerm dotLength(JavaDLTerm a) {
        return func(theories.getHeapLDT().getLength(), a);
    }


    @Override
    public JavaDLTerm created(JavaDLTerm h, JavaDLTerm o) {
        return equals(select(theories.getBooleanLDT().targetSort(),
                             h,
                             o,
                             func(theories.getHeapLDT().getCreated())),
                      TRUE());
    }


    @Override
    public JavaDLTerm created(JavaDLTerm o) {
        return created(getBaseHeap(), o);
    }

    @Override
    public JavaDLTerm initialized(JavaDLTerm o) {
        return equals(dot(theories.getBooleanLDT().targetSort(),
                o,
                theories.getHeapLDT().getInitialized()),
                TRUE());
    }


    @Override
    public JavaDLTerm classPrepared(Sort classSort) {
        return equals(staticDot(theories.getBooleanLDT().targetSort(),
                theories.getHeapLDT().getClassPrepared(classSort,
                        services)),
                        TRUE());
    }

    @Override
    public JavaDLTerm classInitialized(Sort classSort) {
        return equals(staticDot(theories.getBooleanLDT().targetSort(),
                theories.getHeapLDT().getClassInitialized(classSort,
                        services)),
                        TRUE());
    }

    @Override
    public JavaDLTerm classInitializationInProgress(Sort classSort) {
        return equals(staticDot(theories.getBooleanLDT().targetSort(),
                theories.getHeapLDT()
                .getClassInitializationInProgress(classSort,
                        services)),
                        TRUE());
    }


    @Override
    public JavaDLTerm classErroneous(Sort classSort) {
        return equals(staticDot(theories.getBooleanLDT().targetSort(),
                theories.getHeapLDT().getClassErroneous(classSort,
                        services)),
                        TRUE());
    }


    @Override
    public JavaDLTerm store(JavaDLTerm h, JavaDLTerm o, JavaDLTerm f, JavaDLTerm v) {
        return func(theories.getHeapLDT().getStore(),
                h, o, f, v);
    }


    @Override
    public JavaDLTerm create(JavaDLTerm h, JavaDLTerm o) {
        return func(theories.getHeapLDT().getCreate(),
                 new JavaDLTerm[]{h, o});
    }


    @Override
    public JavaDLTerm anon(JavaDLTerm h1, JavaDLTerm s, JavaDLTerm h2) {
    return func(theories.getHeapLDT().getAnon(),
            h1, s, h2);
    }


    @Override
    public JavaDLTerm fieldStore(
            TermServices services,
            JavaDLTerm o, Function f, JavaDLTerm v) {
        return store(getBaseHeap(), o, func(f), v);
    }


    @Override
    public JavaDLTerm staticFieldStore(Function f, JavaDLTerm v) {
    return fieldStore(services, NULL(), f, v);
    }


    @Override
    public JavaDLTerm arrayStore(JavaDLTerm o, JavaDLTerm i, JavaDLTerm v) {
        return store(getBaseHeap(),
                o,
                 func(theories.getHeapLDT().getArr(), i),
                 v);
    }


//    @Override
    public JavaDLTerm reachableValue(JavaDLTerm h,
                               JavaDLTerm t,
                               KeYJavaType kjt) {
        assert t.sort().extendsTrans(kjt.getSort()) || t.sort() instanceof ProgramSVSort;
        final Sort s = t.sort() instanceof ProgramSVSort ? kjt.getSort() : t.sort();
        final IntegerLDT intLDT = theories.getIntegerLDT();
        final LocSetLDT setLDT = theories.getLocSetLDT();
        if (s.extendsTrans(services.getProgramServices().getJavaInfo().objectSort())) {
            return orSC(equals(t, NULL()), created(h, t));
        } else if(s.equals(setLDT.targetSort())) {
            return createdInHeap(t, h);
        } else if(s.equals(intLDT.targetSort()) && kjt.getProgramType() != PrimitiveType.JAVA_BIGINT) {
            return func(intLDT.getInBounds(kjt.getProgramType()), t);
        } else {
            return tt();
        }
    }


//    @Override
    public JavaDLTerm reachableValue(JavaDLTerm t, KeYJavaType kjt) {
        return reachableValue(getBaseHeap(), t, kjt);
    }


//    @Override
    public JavaDLTerm reachableValue(ProgramVariable pv) {
        return reachableValue(var(pv), pv.getKeYJavaType());
    }


    @Override
    public JavaDLTerm frame(JavaDLTerm heapTerm, Map<JavaDLTerm,JavaDLTerm> normalToAtPre,
                  JavaDLTerm mod) {
        final Sort objectSort = services.getProgramServices().getJavaInfo().objectSort();
        final Sort fieldSort = theories.getHeapLDT()
                .getFieldSort();

        final Name objVarName   = new Name(newName("o"));
        final Name fieldVarName = new Name(newName("f"));
        final LogicVariable objVar
        = new LogicVariable(objVarName, objectSort);
        final LogicVariable fieldVar
        = new LogicVariable(fieldVarName, fieldSort);
        final JavaDLTerm objVarTerm = var(objVar);
        final JavaDLTerm fieldVarTerm = var(fieldVar);

        final OpReplacer or = new OpReplacer(normalToAtPre, tf);
        final JavaDLTerm modAtPre = or.replace(mod);
        final JavaDLTerm createdAtPre = or.replace(created(heapTerm, objVarTerm));

        ImmutableList<QuantifiableVariable> quantVars =
                ImmutableSLList.<QuantifiableVariable>nil();
        quantVars = quantVars.append(objVar);
        quantVars = quantVars.append(fieldVar);
        // selects on permission heaps have to be explicitly typed as field type narrowing
        // does not follow Java typing for the permission heap
        boolean permissionHeap =
            heapTerm.op() == theories.getHeapLDT().getPermissionHeap();
        return all(quantVars,
                or(elementOf(objVarTerm,
                        fieldVarTerm,
                        modAtPre),
                        and(not(equals(objVarTerm, NULL())),
                                not(createdAtPre)),
                                equals(select(permissionHeap ? theories.getPermissionLDT().targetSort() : SortImpl.ANY,
                                        heapTerm,
                                        objVarTerm,
                                        fieldVarTerm),
                                        select(permissionHeap ? theories.getPermissionLDT().targetSort() : SortImpl.ANY,
                                                or.replace(heapTerm),
                                                objVarTerm,
                                                fieldVarTerm))));
    }

    /**
     * Returns the framing condition that the resulting heap is identical (i.e.
     * has the same value in all locations) to the before-heap.
     *
     * @see #frame(JavaDLTerm, Map, JavaDLTerm)
     */
    @Override
    public JavaDLTerm frameStrictlyEmpty(JavaDLTerm heapTerm, Map<JavaDLTerm,JavaDLTerm> normalToAtPre) {
        final Sort objectSort = services.getProgramServices().getJavaInfo().objectSort();
        final Sort fieldSort = theories.getHeapLDT()
                .getFieldSort();

        final Name objVarName   = new Name(newName("o"));
        final Name fieldVarName = new Name(newName("f"));
        final LogicVariable objVar = new LogicVariable(objVarName, objectSort);
        final LogicVariable fieldVar = new LogicVariable(fieldVarName, fieldSort);
        final JavaDLTerm objVarTerm = var(objVar);
        final JavaDLTerm fieldVarTerm = var(fieldVar);

        final OpReplacer or = new OpReplacer(normalToAtPre, tf);

        ImmutableList<QuantifiableVariable> quantVars =
                ImmutableSLList.<QuantifiableVariable>nil();
        quantVars = quantVars.append(objVar);
        quantVars = quantVars.append(fieldVar);

        // see above
        boolean permissionHeap = heapTerm.op() == theories.getHeapLDT().getPermissionHeap();

        return all(quantVars,
                equals(select(permissionHeap ? theories.getPermissionLDT().targetSort() : SortImpl.ANY,
                        heapTerm,
                        objVarTerm,
                        fieldVarTerm),
                        select(permissionHeap ? theories.getPermissionLDT().targetSort() : SortImpl.ANY,
                                or.replace(heapTerm),
                                objVarTerm,
                                fieldVarTerm)));
    }

//    @Override
    public JavaDLTerm anonUpd(LocationVariable heap, JavaDLTerm mod, JavaDLTerm anonHeap) {
        return elementary(heap, anon(var(heap), mod, anonHeap));
    }


    @Override
    public JavaDLTerm forallHeaps(TermServices services, JavaDLTerm t) {
        final HeapLDT heapLDT = theories.getHeapLDT();
        final LogicVariable heapLV
        = new LogicVariable(new Name("h"), heapLDT.targetSort());
        final Map<LocationVariable, LogicVariable> map
        = new LinkedHashMap<LocationVariable, LogicVariable>();
        map.put(heapLDT.getHeap(), heapLV);
        final OpReplacer or = new OpReplacer(map, tf);
        t = or.replace(t);
        return all(heapLV, t);
    }


    //-------------------------------------------------------------------------
    //reachability operators
    //-------------------------------------------------------------------------

    @Override
    public JavaDLTerm acc(JavaDLTerm h, JavaDLTerm s, JavaDLTerm o1, JavaDLTerm o2) {
    return func(theories.getHeapLDT().getAcc(),
            h, s, o1, o2);
    }


    @Override
    public JavaDLTerm reach(JavaDLTerm h,
                  JavaDLTerm s,
                  JavaDLTerm o1,
                  JavaDLTerm o2,
                  JavaDLTerm n) {
    return func(theories.getHeapLDT().getReach(),
            h, s, o1, o2, n);
    }


    //-------------------------------------------------------------------------
    //sequence operators
    //-------------------------------------------------------------------------

    @Override
    public JavaDLTerm seqGet(Sort asSort, JavaDLTerm s, JavaDLTerm idx) {
        return func(theories.getSeqLDT().getSeqGet(asSort, services),
                    s,
                    idx);
    }


    @Override
    public JavaDLTerm seqLen(JavaDLTerm s) {
        return func(theories.getSeqLDT().getSeqLen(), s);
    }

    /** Function representing the least index of an element x in a sequence s (or underspecified) */
    @Override
    public JavaDLTerm indexOf(JavaDLTerm s, JavaDLTerm x){
        return func(theories.getSeqLDT().getSeqIndexOf(),s,x);
    }


    @Override
    public JavaDLTerm seqEmpty() {
        return func(theories.getSeqLDT().getSeqEmpty());
    }

    @Override
    public JavaDLTerm seqSingleton(JavaDLTerm x) {
        return func(theories.getSeqLDT().getSeqSingleton(), x);
    }

    @Override
    public JavaDLTerm seqConcat(JavaDLTerm s, JavaDLTerm s2) {
        if (s == seqEmpty()) {
            return s2;
        } else if (s2 == seqEmpty()) {
            return s;
        } else {
            return func(theories.getSeqLDT().getSeqConcat(),
                        s,
                        s2);
        }
    }

    @Override
    public JavaDLTerm seq(JavaDLTerm... terms) {
        JavaDLTerm result = seqEmpty();
        for (JavaDLTerm term : terms) {
            result = seqConcat(result, seqSingleton(term));
        }
        return result;
    }


    @Override
    public JavaDLTerm seq(ImmutableList<JavaDLTerm> terms) {
        JavaDLTerm result = seqEmpty();
        for (JavaDLTerm term : terms) {
            result = seqConcat(result, seqSingleton(term));
        }
        return result;
    }

    @Override
    public JavaDLTerm seqSub(JavaDLTerm s, JavaDLTerm from, JavaDLTerm to) {
    return func(theories.getSeqLDT().getSeqSub(), s, from, to);
    }

    @Override
    public JavaDLTerm seqReverse(JavaDLTerm s) {
    return func(theories.getSeqLDT().getSeqReverse(), s);
    }

    //-------------------------------------------------------------------------
    // misc    (moved from key.util.MiscTools)
    //-------------------------------------------------------------------------



    @Override
    public ImmutableSet<JavaDLTerm> unionToSet(JavaDLTerm s) {
    final LocSetLDT setLDT = theories.getLocSetLDT();
    assert s.sort().equals(setLDT.targetSort());
    final Function union = setLDT.getUnion();
    ImmutableSet<JavaDLTerm> result = DefaultImmutableSet.<JavaDLTerm>nil();
        ImmutableList<JavaDLTerm> workingList = ImmutableSLList.<JavaDLTerm>nil().prepend(s);
        while(!workingList.isEmpty()) {
            JavaDLTerm f = workingList.head();
            workingList = workingList.tail();
            if(f.op() == union) {
                workingList = workingList.prepend(f.sub(1)).prepend(f.sub(0));
            } else {
                result = result.add(f);
            }
        }
        return result;
    }



    /**
     * Removes leading updates from the passed term.
     */
    public static JavaDLTerm goBelowUpdates(JavaDLTerm term) {
        while (term.op() instanceof UpdateApplication) {
            term = UpdateApplication.getTarget(term);
        }
        return term;
    }

    /**
     * Removes leading updates from the passed term.
     */
    public static Pair<ImmutableList<JavaDLTerm>, JavaDLTerm> goBelowUpdates2(
            JavaDLTerm term) {
        ImmutableList<JavaDLTerm> updates = ImmutableSLList.<JavaDLTerm> nil();
        while (term.op() instanceof UpdateApplication) {
            updates = updates.append(UpdateApplication.getUpdate(term));
            term = UpdateApplication.getTarget(term);
        }
        return new Pair<ImmutableList<JavaDLTerm>, JavaDLTerm>(updates, term);
    }



    @Override
    public JavaDLTerm seqDef(QuantifiableVariable qv,
                       JavaDLTerm a,
                       JavaDLTerm b,
                       JavaDLTerm t) {
        return func(theories.getSeqLDT().getSeqDef(),
                    new JavaDLTerm[]{a, b, t},
                    new ImmutableArray<QuantifiableVariable>(qv));
    }

    @Override
    public JavaDLTerm values(){
        return func(theories.getSeqLDT().getValues());
    }

    /**
      * Returns the {@link Sort}s of the given {@link JavaDLTerm}s.
      * @param terms The given {@link JavaDLTerm}s.
      * @return The {@link JavaDLTerm} {@link Sort}s.
      */
    @Override
    public ImmutableList<Sort> getSorts(Iterable<JavaDLTerm> terms) {
       ImmutableList<Sort> result = ImmutableSLList.<Sort>nil();
       for (JavaDLTerm t : terms) {
          result = result.append(t.sort());
       }
       return result;
    }

   /**
    * Similar behavior as {@link #imp(JavaDLTerm, JavaDLTerm)} but simplifications are not
    * performed if {@link TermLabel}s would be lost.
    * @param t1 The left side.
    * @param t2 The right side.
    * @return The created {@link JavaDLTerm}.
    */
   @Override
public JavaDLTerm impPreserveLabels(JavaDLTerm t1, JavaDLTerm t2) {
      if ((t1.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) &&
          (!t1.hasLabels() && !t2.hasLabels())) {
         return tt();
      }
      else if (t1.op() == Junctor.TRUE && !t1.hasLabels()) {
         return t2;
      }
      else if (t2.op() == Junctor.FALSE && !t2.hasLabels()) {
         return notPreserveLabels(t1);
      }
      else {
         return tf.createTerm(Junctor.IMP, t1, t2);
      }
   }
    
   /**
    * Similar behavior as {@link #not(JavaDLTerm)} but simplifications are not
    * performed if {@link TermLabel}s would be lost.
    * @param t The child {@link JavaDLTerm}.
    * @return The created {@link JavaDLTerm}.
    */
   @Override
public JavaDLTerm notPreserveLabels(JavaDLTerm t) {
      if (t.op() == Junctor.TRUE && !t.hasLabels()) {
         return ff();
      }
      else if (t.op() == Junctor.FALSE && !t.hasLabels()) {
         return tt();
      }
      else if (t.op() == Junctor.NOT && !t.hasLabels()) {
         return t.sub(0);
      }
      else {
         return tf.createTerm(Junctor.NOT, t);
      }
   }

   /**
    * Similar behavior as {@link #and(Iterable)} but simplifications are not
    * performed if {@link TermLabel}s would be lost.
    * @param subTerms The sub {@link JavaDLTerm}s.
    * @return The created {@link JavaDLTerm}.
    */
   @Override
public JavaDLTerm andPreserveLabels(Iterable<JavaDLTerm> subTerms) {
      JavaDLTerm result = tt();
      for (JavaDLTerm sub : subTerms) {
         result = andPreserveLabels(result, sub);
      }
      return result;
   }

   /**
    * Similar behavior as {@link #and(JavaDLTerm, JavaDLTerm)} but simplifications are not
    * performed if {@link TermLabel}s would be lost.
    * @param t1 The left side.
    * @param t2 The right side.
    * @return The created {@link JavaDLTerm}.
    */
   @Override
public JavaDLTerm andPreserveLabels(JavaDLTerm t1, JavaDLTerm t2) {
      if ((t1.op() == Junctor.FALSE || t2.op() == Junctor.FALSE) &&
          (!t1.hasLabels() && !t2.hasLabels())) {
         return ff();
      }
      else if (t1.op() == Junctor.TRUE && !t1.hasLabels()) {
         return t2;
      }
      else if (t2.op() == Junctor.TRUE && !t2.hasLabels()) {
         return t1;
      }
      else {
         return tf.createTerm(Junctor.AND, t1, t2);
      }
   }

   /**
    * Similar behavior as {@link #or(Iterable)} but simplifications are not
    * performed if {@link TermLabel}s would be lost.
    * @param subTerms The sub {@link JavaDLTerm}s.
    * @return The created {@link JavaDLTerm}.
    */
   @Override
public JavaDLTerm orPreserveLabels(Iterable<JavaDLTerm> subTerms) {
      JavaDLTerm result = ff();
      for (JavaDLTerm sub : subTerms) {
         result = orPreserveLabels(result, sub);
      }
      return result;
   }

   /**
    * Similar behavior as {@link #or(JavaDLTerm, JavaDLTerm)} but simplifications are not
    * performed if {@link TermLabel}s would be lost.
    * @param t1 The left side.
    * @param t2 The right side.
    * @return The created {@link JavaDLTerm}.
    */
   @Override
public JavaDLTerm orPreserveLabels(JavaDLTerm t1, JavaDLTerm t2) {
      if ((t1.op() == Junctor.TRUE || t2.op() == Junctor.TRUE) &&
          (!t1.hasLabels() && !t2.hasLabels())) {
         return tt();
      }
      else if (t1.op() == Junctor.FALSE && !t1.hasLabels()) {
         return t2;
      }
      else if (t2.op() == Junctor.FALSE && !t2.hasLabels()) {
         return t1;
      }
      else {
         return tf.createTerm(Junctor.OR, t1, t2);
      }
   }

    //-------------------------------------------------------------------------
    // information flow operators
    //-------------------------------------------------------------------------

    @Override
    public JavaDLTerm eqAtLocs(TermServices services,
                         JavaDLTerm heap1,
                         JavaDLTerm locset1,
                         JavaDLTerm heap2,
                         JavaDLTerm locset2) {
        return (locset1.equals(empty())
                && locset2.equals(empty()))
                ? tt
                        : func((Function) services.getNamespaces().functions().lookup(new Name(
                                "__EQUALS__LOCS__")), // TODO: define string constant elsewhere
                                heap1, locset1, heap2, locset2);
    }


    @Override
    public JavaDLTerm eqAtLocsPost(TermServices services,
                             JavaDLTerm heap1_pre,
                             JavaDLTerm heap1_post,
                             JavaDLTerm locset1,
                             JavaDLTerm heap2_pre,
                             JavaDLTerm heap2_post,
                             JavaDLTerm locset2) {
        return (locset1.equals(empty())
                && locset2.equals(empty()))
                ? tt
                        : func((Function) services.getNamespaces().functions().lookup(new Name(
                                "__EQUALS__LOCS__POST__")), // TODO: define string constant elsewhere
                                heap1_pre, heap1_post, locset1, heap2_pre, heap2_post, locset2);
    }
}