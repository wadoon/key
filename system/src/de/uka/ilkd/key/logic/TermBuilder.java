// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.logic;


import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.keyabs.logic.ldt.IHeapLDT;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

/**
 * <p>Use this class if you intend to build complex terms by hand. It is
 * more convenient than the @link{TermFactory} class.</p>
 *
 * <p>Attention: some methods of this class try to simplify some terms. So if you
 * want to be sure that the term looks exactly as you built it, you
 * will have to use the TermFactory.</p>
 */
public abstract class TermBuilder<S extends IServices> {
        
    private static final TermFactory tf = TermFactory.DEFAULT;    
    private static final Term tt = TermFactory.DEFAULT.createTerm(Junctor.TRUE); 
    private static final Term ff = TermFactory.DEFAULT.createTerm(Junctor.FALSE); 

    protected TermBuilder() {
    }


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
     * @param services
     *            the services to be used for parsing
     */
    public abstract Term parseTerm(String s, IServices services)
        throws ParserException;

    /**
     * Parses the given string that represents the term (or createTerm) using the
     * provided namespaces.
     *
     * @param s
     *            the String to parse
     * @param services
     *            the services to be used for parsing
     * @param namespaces
     *            the namespaces used for name lookup.
     */
    public abstract Term parseTerm(String s, IServices services, NamespaceSet namespaces)
            throws ParserException; 
    
    
    //-------------------------------------------------------------------------
    //naming
    //-------------------------------------------------------------------------

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
    public String newName(IServices services, String baseName) {
    final Name savedName = services.getNameRecorder().getProposal();
    if(savedName != null) {
        return savedName.toString();
    }

        final NamespaceSet namespaces = services.getNamespaces();

        int i = 0;
        Name result = new Name(baseName);
        while(namespaces.lookup(result) != null || 
        		services.getNameRecorder().getProposals().contains(result)) {
            result = new Name(baseName + "_" + i++);
        }

        services.getNameRecorder().addProposal(result);

        return result.toString();
    }


    /**
     * Returns an available name constructed by affixing a counter to a self-
     * chosen base name for the passed sort.
     */
    public String newName(IServices services, Sort sort) {
    return newName(services, shortBaseName(sort));
    }




    //-------------------------------------------------------------------------
    //common variable constructions
    //-------------------------------------------------------------------------

    /**
     * Creates a program variable for the atPre heap. Take care to register it
     * in the namespaces.
     */
    public LocationVariable heapAtPreVar(IServices services,
	    				                 String baseName,
                                         Sort sort,
                                         boolean makeNameUnique) {
        assert sort != null;
    if(makeNameUnique) {
        baseName = newName(services, baseName);
    }
    return new LocationVariable(new ProgramElementName(baseName),
                            new KeYJavaType(sort));
    }

    //-------------------------------------------------------------------------
    //constructors for special classes of term operators
    //-------------------------------------------------------------------------

    public Term var(LogicVariable v) {
        return tf.createTerm(v);
    }

    public Term var(IProgramVariable v) {
        return tf.createTerm(v);
    }

    public Term var(ProgramVariable v) { 
//	if(v.isMember()) {
//	    throw new TermCreationException(
//		    "Cannot create term for \"member\" "
//		    + "program variable \"" + v + "\". Use field symbols "
//		    + "like your mother told you!");
//	}
        return tf.createTerm(v);
    }


    public ImmutableList<Term> var(ProgramVariable ... vs) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (ProgramVariable v : vs) {
            result = result.append(var(v));
        }
        return result;
    }


    public ImmutableList<Term> var(Iterable<ProgramVariable> vs) {
    ImmutableList<Term> result = ImmutableSLList.<Term>nil();
    for (ProgramVariable v : vs) {
        result = result.append(var(v));
    }
        return result;
    }


    public Term var(SchemaVariable v) {
    return tf.createTerm(v);
    }


    public Term var(ParsableVariable v) {
    return tf.createTerm(v);
    }


    public Term func(Function f) {
        return tf.createTerm(f);
    }


    public Term func(Function f, Term s) {
        return tf.createTerm(f, s);
    }


    public Term func(Function f, Term s1, Term s2) {
        return tf.createTerm(f, s1, s2);
    }


    public Term func(Function f, Term ... s) {
        return tf.createTerm(f, s, null, null);
    }

    public Term func(IObserverFunction f, Term ... s) {
       return tf.createTerm(f, s, null, null);
   }

    public Term func(Function f,
                 Term[] s,
                 ImmutableArray<QuantifiableVariable> boundVars) {
        return tf.createTerm(f, s, boundVars, null);
    }


    public Term prog(Modality mod, JavaBlock jb, Term t) {
    return tf.createTerm(mod, new Term[]{t}, null, jb);
    }


    public Term box(JavaBlock jb, Term t) {
        return prog(Modality.BOX, jb, t);
    }


    public Term dia(JavaBlock jb, Term t) {
        return prog(Modality.DIA, jb, t);
    }


    public Term ife(Term cond, Term _then, Term _else) {
        return tf.createTerm(IfThenElse.IF_THEN_ELSE,
                         new Term[]{cond, _then, _else});
    }
    public Term cast(IServices services, Sort s, Term t) {
	return tf.createTerm(s.getCastSymbol(services), t);
    }


    public Term tt() {
        return tt;
    }


    public Term ff() {
        return ff;
    }


    public Term all(QuantifiableVariable qv, Term t) {
        return tf.createTerm(Quantifier.ALL,
                             new ImmutableArray<Term>(t),
                             new ImmutableArray<QuantifiableVariable>(qv),
                             null);
    }


    public Term all(Iterable<QuantifiableVariable> qvs, Term t) {
        Term result = t;
        for (QuantifiableVariable fv : qvs) {
            result = all(fv, result);
        }
        return result;
    }


    public Term allClose(Term t) {
    return all(t.freeVars(), t);
    }

    /**
     * Removes universal quantifiers from a formula.
     */
    public Term open(Term formula) {
    assert formula.sort() == Sort.FORMULA;
    if(formula.op() == Quantifier.ALL) {
        return open(formula.sub(0));
    } else {
        return formula;
    }
    }


    public Term ex(QuantifiableVariable qv, Term t) {
    return tf.createTerm(Quantifier.EX,
                 new ImmutableArray<Term>(t),
                 new ImmutableArray<QuantifiableVariable>(qv),
                 null);
    }


    public Term ex(Iterable<QuantifiableVariable> qvs, Term t) {
        Term result = t;
        for (QuantifiableVariable fv : qvs) {
            result = ex(fv, result);
        }
        return result;
    }


    public Term bsum(QuantifiableVariable qv,
                     Term a,
                     Term b,
                     Term t,
                     IServices services) {
        Function bsum = services.getTypeConverter().getIntegerLDT().getBsum();
        return func(bsum,
                    new Term[]{a, b, t},
                    new ImmutableArray<QuantifiableVariable>(qv));
    }



    /** Constructs a bounded product comprehension expression. */
    public Term bprod(QuantifiableVariable qv,
                     Term a,
                     Term b,
                     Term t,
                     Services services) {
        Function bprod = services.getTypeConverter().getIntegerLDT().getBprod();
        return func(bprod,
                    new Term[]{a, b, t},
                    new ImmutableArray<QuantifiableVariable>(qv));
    }


    public Term min(QuantifiableVariable qv, Term t, Services services) {
        Function min = services.getTypeConverter().getIntegerLDT().getMin();
        return tf.createTerm(min,
                           new ImmutableArray<Term>(t),
                           new ImmutableArray<QuantifiableVariable>(qv),
                           null);
    }


    public Term max(QuantifiableVariable qv, Term t, Services services) {
        Function max = services.getTypeConverter().getIntegerLDT().getMax();
        return tf.createTerm(max,
                           new ImmutableArray<Term>(t),
                           new ImmutableArray<QuantifiableVariable>(qv),
                           null);
    }


    public Term not(Term t) {
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


    public Term and(Term t1, Term t2) {
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


    public Term and(Term ... subTerms) {
        Term result = tt();
        for(Term sub : subTerms) {
        result = and(result, sub);
    }
        return result;
    }


    public Term and(Iterable<Term> subTerms) {
    Term result = tt();
    for(Term sub : subTerms) {
        result = and(result, sub);
    }
    return result;
    }


    public Term or(Term t1, Term t2) {
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


    public Term or(Term... subTerms) {
        Term result = ff();
        for(Term sub : subTerms) {
            result = or(result, sub);
        }
        return result;
    }


    public Term or(Iterable<Term> subTerms) {
    Term result = ff();
    for(Term sub : subTerms) {
        result = or(result, sub);
    }
    return result;
    }


    public Term imp(Term t1, Term t2) {
    if(t1.op() == Junctor.FALSE || t2.op() == Junctor.TRUE) {
        return tt();
    } else if(t1.op() == Junctor.TRUE) {
        return t2;
    } else if(t2.op() == Junctor.FALSE) {
        return not(t1);
    } else {
        return tf.createTerm(Junctor.IMP, t1, t2);
    }
    }


    /**
     * Creates a term with the correct equality symbol for
     * the sorts involved
     */
    public Term equals(Term t1, Term t2) {
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
     * @param substTerm the Term that replaces substVar
     * @param origTerm the Term that is substituted
     */
    public Term subst(SubstOp op,
                  QuantifiableVariable substVar,
                  Term substTerm,
                  Term origTerm) {
    return tf.createTerm(op,
                     new ImmutableArray<Term>(new Term[]{substTerm, origTerm}),
                     new ImmutableArray<QuantifiableVariable>(substVar),
                     null);
    }


    public Term instance(IServices services, Sort s, Term t) {
    return equals(func(s.getInstanceofSymbol(services), t),
              TRUE(services));
    }


    public Term exactInstance(IServices services, Sort s, Term t) {
    return equals(func(s.getExactInstanceofSymbol(services), t),
              TRUE(services));
    }


    /**
     * If a is a boolean literal, the method returns the literal as a Formula.
     */
    public Term convertToFormula(Term a, IServices services) {
        BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
        if (a.sort() == Sort.FORMULA) {
            return a;
        } else if (a.sort() == booleanLDT.targetSort()) {
            // special case where a is the result of convertToBoolean
            if (a.op() == IfThenElse.IF_THEN_ELSE) {
                assert a.subs().size() == 3;
                assert a.sub(0).sort() == Sort.FORMULA;
                if (a.sub(1) == booleanLDT.getTrueTerm() && a.sub(2) == booleanLDT.getFalseTerm())
                    return a.sub(0);
                else if (a.sub(1) == booleanLDT.getFalseTerm() && a.sub(2) == booleanLDT.getTrueTerm())
                    return not(a.sub(0));
            }
            return equals(a, TRUE(services));
        } else {
            throw new TermCreationException("Term " + a + " cannot be converted"
                                            + " into a formula.");
        }
    }

    /** For a formula a, convert it to a boolean expression. */
    public Term convertToBoolean(Term a, Services services){
        BooleanLDT booleanLDT = services.getTypeConverter().getBooleanLDT();
        if (a.sort() == booleanLDT.targetSort()) {
            return a;
        } else if (a.sort() == Sort.FORMULA) {
            // special case where a is the result of convertToFormula
            if (a.op() == Equality.EQUALS && a.sub(1) == booleanLDT.getTrueTerm() ) {
                return a.sub(0);
            }
            return ife(a, TRUE(services), FALSE(services));
        } else {
            throw new TermCreationException("Term " + a + " cannot be converted"
                    + " into a boolean.");
}
    }


    //-------------------------------------------------------------------------
    //updates
    //-------------------------------------------------------------------------
    public Term elementary(IServices services,
        UpdateableOperator lhs,
        Term rhs) {
    ElementaryUpdate eu = ElementaryUpdate.getInstance(lhs);
    return tf.createTerm(eu, rhs);
    }


    public Term elementary(S services, Term lhs, Term rhs) {
    IHeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
    if(lhs.op() instanceof UpdateableOperator) {
        assert lhs.arity() == 0 : "uh oh: " + lhs;
        return elementary(services, (UpdateableOperator)lhs.op(), rhs);
    } else if(heapLDT.getSortOfSelect(lhs.op()) != null
          && lhs.sub(0).op().equals(heapLDT.getHeap())) {
        final Term heapTerm   = lhs.sub(0);
        final Term objectTerm = lhs.sub(1);
        final Term fieldTerm  = lhs.sub(2);

        final Term fullRhs = store(services,
                                   heapTerm,
                               objectTerm,
                               fieldTerm,
                               rhs);
        return elementary(services, heapLDT.getHeap(), fullRhs);
    } else {
        throw new TermCreationException("Not a legal lhs: " + lhs);
    }
    }


    public Term elementary(S services, Term heapTerm) {
        return elementary(services, getBaseHeap(services), heapTerm);
    }


    public Term elementary(S services, LocationVariable heap) {
        return elementary(services, var(heap));
    }


    public Term skip() {
    return tf.createTerm(UpdateJunctor.SKIP);
    }


    public Term parallel(Term u1, Term u2) {
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


    public Term parallel(Term... updates) {
    Term result = skip();
    for(int i = 0; i < updates.length; i++) {
        result = parallel(result, updates[i]);
    }
    return result;
    }


    public Term parallel(ImmutableList<Term> updates) {
    return parallel(updates.toArray(new Term[updates.size()]));
    }

    public Term parallel(S services, Term[] lhss, Term[] values) {
    if(lhss.length != values.length) {
        throw new TermCreationException(
            "Tried to create parallel update with "
            + lhss.length + " locs and " + values.length + " values");
    }
    Term[] updates = new Term[lhss.length];
    for(int i = 0; i < updates.length; i++) {
        updates[i] = elementary(services, lhss[i], values[i]);
    }
    return parallel(updates);
    }


    public Term parallel(S services,
                         Iterable<Term> lhss,
                         Iterable<Term> values) {
        ImmutableList<Term> updates = ImmutableSLList.<Term>nil();
        Iterator<Term> lhssIt = lhss.iterator();
        Iterator<Term> rhssIt = values.iterator();
        while (lhssIt.hasNext()) {
            assert rhssIt.hasNext();
            updates = updates.append(elementary(services, lhssIt.next(),
                                                rhssIt.next()));
        }
        return parallel(updates);
    }


    public Term sequential(Term u1, Term u2) {
    return parallel(u1, apply(u1, u2));
    }


    public Term sequential(Term[] updates) {
    if(updates.length == 0) {
        return skip();
    } else {
        Term result = updates[updates.length - 1];
        for(int i = updates.length - 2; i >= 0; i++) {
        result = sequential(updates[i], result);
        }
        return result;
    }
    }


    public Term sequential(ImmutableList<Term> updates) {
    if(updates.isEmpty()) {
        return skip();
    } else if(updates.size() == 1) {
        return updates.head();
    } else {
        return sequential(updates.head(), sequential(updates.tail()));
    }
    }


    public Term apply(Term update, Term target) {
    if(update.sort() != Sort.UPDATE) {
        throw new TermCreationException("Not an update: " + update);
    } else if(update.op() == UpdateJunctor.SKIP) {
        return target;
    } else if(target.equals(tt())) {
            return tt();
        } else {
        return tf.createTerm(UpdateApplication.UPDATE_APPLICATION,
                     update,
                     target);
    }
    }

    public Term applyElementary(S services,
	                        Term loc,
	                        Term value,
	                        Term target) {
	return apply(elementary(services, loc, value), target);
    }


    public Term applyElementary(S services,
	                        Term heap,
	                        Term target) {
	return apply(elementary(services, heap), target);
    }


    public ImmutableList<Term> applyElementary(S services,
	                        Term heap,
	                        Iterable<Term> targets) {
        ImmutableList<Term> result = ImmutableSLList.<Term>nil();
        for (Term target : targets) {
            result = result.append(apply(elementary(services, heap), target));
        }
    return result;
    }


    public Term applyParallel(Term[] updates, Term target) {
	return apply(parallel(updates), target);
    }
    
    
    public Term applyParallel(ImmutableList<Term> updates, Term target) {	
	return apply(parallel(updates), target);
    }
    
    
    public Term applyParallel(S services, 
	                      Term[] lhss, 
	                      Term[] values, 
	                      Term target) {
	return apply(parallel(services, lhss, values), target);
    }
    
    
    public Term applySequential(Term[] updates, Term target) {
    if(updates.length == 0) {
        return target;
    } else {
        ImmutableList<Term> updateList = ImmutableSLList.<Term>nil()
                                            .append(updates)
                                            .tail();
        return apply(updates[0],
                 applySequential(updateList, target));
    }
    }


    public Term applySequential(ImmutableList<Term> updates, Term target) {
    if(updates.isEmpty()) {
        return target;
    } else {
        return apply(updates.head(),
                 applySequential(updates.tail(), target));
    }
    }



    //-------------------------------------------------------------------------
    //boolean operators
    //-------------------------------------------------------------------------
    public Term TRUE(IServices services) {
        return services.getTypeConverter().getBooleanLDT().getTrueTerm();
    }
    
    
    public Term FALSE(IServices services) {
        return services.getTypeConverter().getBooleanLDT().getFalseTerm();
    }



    //-------------------------------------------------------------------------
    //integer operators
    //-------------------------------------------------------------------------
    public Term geq(Term t1, Term t2, S services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getGreaterOrEquals(), t1, t2);
    }
    
    
    public Term gt(Term t1, Term t2, S services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getGreaterThan(), t1, t2);
    }
    
    
    public Term lt(Term t1, Term t2, S services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getLessThan(), t1, t2);
    }    
    
    
    public Term leq(Term t1, Term t2, S services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return func(integerLDT.getLessOrEquals(), t1, t2);
    }    
    
    
    public Term zero(IServices services) {
	return services.getTypeConverter().getIntegerLDT().zero();
    }

    
    public Term one(IServices services) {
        return services.getTypeConverter().getIntegerLDT().one();
    }

    /**
     * @param services Services which contains the number-functions
     * @param numberString String representing an integer
     * @return Term in Z-Notation representing the given number
     */
    public Term zTerm(IServices services, String numberString) {
        Operator v;
        Term t;
        boolean negate = false;
        int j = 0;

        Namespace funcNS = services.getNamespaces().functions();

        if (numberString.substring(0,1).equals("-")) {
            negate = true;
            j=1;
        }
        v=(Function)  funcNS.lookup(new Name("#"));
        t = func((Function)v);
        v = (Function) funcNS.lookup(new Name(numberString.substring(j,j+1)));
        t = func((Function)v,t);
        for(int i=j+1;i<numberString.length();i++){
            v = (Function)funcNS.lookup(new Name(numberString.substring(i,i+1)));
            t = func((Function)v,t);
        }
        if (negate) {
            v=(Function) funcNS.lookup(new Name("neglit"));
            t = func((Function) v, t);
        }
        v = (Function) funcNS.lookup(new Name("Z"));
        t = func((Function)v,t);
        return t;
    }

    public Term add(S services, Term t1, Term t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        final Term zero = integerLDT.zero();
        if(t1.equals(zero)) {
            return t2;
        } else if(t2.equals(zero)) {
            return t1;
        } else {
            return func(integerLDT.getAdd(), t1, t2);
        }
    }

    public Term mul(IServices services, Term t1, Term t2) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        final Term one = integerLDT.one();
        if(t1.equals(one)) {
            return t2;
        } else if(t2.equals(one)) {
            return t1;
        } else {
            return func(integerLDT.getMul(), t1, t2);
        }
    }

    public Term index(S services){
    	return func(services.getTypeConverter().getIntegerLDT().getIndex());
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
    public Term strictlyNothing() {
        return ff();
    }

    public Term empty(IServices services) {
	return func(services.getTypeConverter().getLocSetLDT().getEmpty());
    }
    
    
    public Term allLocs(IServices services) {
	return func(services.getTypeConverter().getLocSetLDT().getAllLocs());
    }    
    
    
    public Term singleton(IServices services, Term o, Term f) {
	return func(services.getTypeConverter().getLocSetLDT().getSingleton(), 
		    o, 
		    f);
    }
    
    
    public Term union(IServices services, Term s1, Term s2) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s1.op() == ldt.getEmpty()) {
	    return s2;
	} else if(s2.op() == ldt.getEmpty()) {
	    return s1;
	} else {
	    return func(ldt.getUnion(), s1, s2);
	}
    }
    
    
    public Term union(IServices services, Term ... subTerms) {
        Term result = empty(services);
        for(Term sub : subTerms) {
        result = union(services, result, sub);
    }
        return result;
    }
    public Term union(IServices services, Iterable<Term> subTerms) {
        Term result = empty(services);
        for(Term sub : subTerms) {
        result = union(services, result, sub);
    }
        return result;
    }

    public Term intersect(IServices services, Term s1, Term s2) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
	    return empty(services);
	} else {
	    return func(ldt.getIntersect(), s1, s2);
	}
    }
    
    
    public Term intersect(IServices services, Term ... subTerms) {
        Term result = empty(services);
        for(Term sub : subTerms) {
        result = intersect(services, result, sub);
    }
        return result;
    }
    public Term intersect(IServices services, Iterable<Term> subTerms) {
        Term result = empty(services);
        for(Term sub : subTerms) {
        result = intersect(services, result, sub);
    }
        return result;
    }

    public Term setMinus(IServices services, Term s1, Term s2) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
	    return s1;
	} else {
	    return func(ldt.getSetMinus(), s1, s2);
	}
    }
    
    
    public Term infiniteUnion(IServices services, 
	                      QuantifiableVariable[] qvs, 
	                      Term s) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	return tf.createTerm(ldt.getInfiniteUnion(), 
		             new Term[]{s}, 
		             new ImmutableArray<QuantifiableVariable>(qvs), 
		             null);
    }
    
    
    public Term guardedInfiniteUnion(IServices services, 
	    			     QuantifiableVariable[] qvs, 
	    			     Term guard, 
	    			     Term s) {
	return infiniteUnion(services, 
		             qvs, 
		             ife(guard, s, empty(services)));
    }
    
    
    public Term setComprehension(IServices services, 
	                         QuantifiableVariable[] qvs, 
	                         Term o, 
	                         Term f) {
	return infiniteUnion(services, qvs, singleton(services, o, f));
    }
    
    
    public Term guardedSetComprehension(IServices services, 
	                         	QuantifiableVariable[] qvs,
	                         	Term guard,
	                         	Term o,
	                         	Term f) {
	return guardedInfiniteUnion(services, 
		                    qvs, 
		                    guard, 
		                    singleton(services, o, f));
    }
    
    
    public Term allFields(IServices services, Term o) {
	return func(services.getTypeConverter().getLocSetLDT().getAllFields(), o);
    }
    
    
    public Term allObjects(IServices services, Term f) {
	return func(services.getTypeConverter().getLocSetLDT().getAllObjects(), f);
    }
    
    
    public Term arrayRange(IServices services, Term o, Term lower, Term upper) {
	return func(services.getTypeConverter().getLocSetLDT().getArrayRange(), 
		    new Term[]{o, lower, upper});
    }        
    
    
    public Term freshLocs(IServices services, Term h) {
	return func(services.getTypeConverter().getLocSetLDT().getFreshLocs(), h);
    }    
    
    
    public Term elementOf(IServices services, Term o, Term f, Term s) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s.op() == ldt.getEmpty()) {
	    return ff();
	} else {
	    return func(ldt.getElementOf(), new Term[]{o, f, s});
	}
    }
    
    
    public Term subset(IServices services, Term s1, Term s2) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s1.op() == ldt.getEmpty()) {
	    return tt();
	} else {
	    return func(ldt.getSubset(), s1, s2);
	}
    }
    
    
    public Term disjoint(IServices services, Term s1, Term s2) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s1.op() == ldt.getEmpty() || s2.op() == ldt.getEmpty()) {
	    return tt();
	} else {
	    return func(ldt.getDisjoint(), s1, s2);
	}
    }
    
    
    public Term createdInHeap(IServices services, Term s, Term h) {
	final LocSetLDT ldt = services.getTypeConverter().getLocSetLDT();
	if(s.op() == ldt.getEmpty()) {
	    return tt();
	} else {
	    return func(ldt.getCreatedInHeap(), s, h);
	}
    }    
    
    
    public Term createdLocs(IServices services) {
        return setMinus(services, 
        	        allLocs(services), 
                        freshLocs(services, getBaseHeap(services))); 
    }    
    
    
    

    //-------------------------------------------------------------------------
    //heap operators
    //-------------------------------------------------------------------------

    public Term NULL(IServices services) {
        return func(services.getTypeConverter().getHeapLDT().getNull());
    }

    public Term select(IServices services, Sort asSort, Term h, Term o, Term f) {
	return func(services.getTypeConverter().getHeapLDT().getSelect(
		    asSort, 
		    services), 
		    new Term[]{h, o, f});
    }

    
    public Term dot(IServices services, Sort asSort, Term o, Term f) {
        return select(services, asSort, getBaseHeap(services), o, f);
    }

    public Term getBaseHeap(IServices services) {
        return var(services.getTypeConverter().getHeapLDT().getHeap());
    }

    public Term dot(IServices services, Sort asSort, Term o, Function f) {
	final Sort fieldSort 
		= services.getTypeConverter().getHeapLDT().getFieldSort();
        return f.sort() == fieldSort
               ? dot(services, asSort, o, func(f))
               : func(f, getBaseHeap(services), o);
    }


    public Term store(IServices services, Term h, Term o, Term f, Term v) {
        return func(services.getTypeConverter().getHeapLDT().getStore(), 
        	    new Term[]{h, o, f, v});
    }


    
    public Term anon(S services, Term h1, Term s, Term h2) {
	return func(services.getTypeConverter().getHeapLDT().getAnon(), 
		    new Term[]{h1, s, h2});
    }
    
               
    public Term fieldStore(S services, Term o, Function f, Term v) {
        return store(services, getBaseHeap(services), o, func(f), v);
    }
    
        
    public Term anonUpd(LocationVariable heap, S services, Term mod, Term anonHeap) {
	return elementary(services,
		          heap,
		          anon(services, 
		               var(heap), 
		               mod, 
		               anonHeap));
    }
    
        
    public Term forallHeaps(S services, Term t) {
	final IHeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
	final LogicVariable heapLV 
		= new LogicVariable(new Name("h"), ((LDT)heapLDT).targetSort());
	final Map<LocationVariable, LogicVariable> map
		= new HashMap<LocationVariable, LogicVariable>();
	map.put(heapLDT.getHeap(), heapLV);
	final OpReplacer or = new OpReplacer(map);
	t = or.replace(t);
	return all(heapLV, t);
    }
    
    public Term wellFormed(Term heap, Services services) {
        return func(services.getTypeConverter().getHeapLDT().getWellFormed(heap.sort()), 
        	    heap);
    }
    
    //-------------------------------------------------------------------------
    //reachability operators
    //-------------------------------------------------------------------------
    public Term acc(S services, Term h, Term s, Term o1, Term o2) {
	return func(services.getTypeConverter().getHeapLDT().getAcc(), 
		    new Term[]{h, s, o1, o2});
    }
    
    
    public Term reach(S services, 
	    	      Term h, 
	    	      Term s, 
	    	      Term o1, 
	    	      Term o2, 
	    	      Term n) {
	return func(services.getTypeConverter().getHeapLDT().getReach(), 
		    new Term[]{h, s, o1, o2, n});
    }    
    
    //-------------------------------------------------------------------------
    //sequence operators
    //-------------------------------------------------------------------------

    public Term seqGet(S services, Sort asSort, Term s, Term idx) {
	return func(services.getTypeConverter().getSeqLDT().getSeqGet(asSort, 
		    						      services), 
		    s,
		    idx);
    }
    
    
    public Term seqLen(S services, Term s) {
	return func(services.getTypeConverter().getSeqLDT().getSeqLen(), s);
    }

    /** Function representing the least index of an element x in a sequence s (or underspecified) */
    public Term indexOf(S services, Term s, Term x){
	return func(services.getTypeConverter().getSeqLDT().getSeqIndexOf(),s,x);
    }
    
    
    public Term seqEmpty(S services) {
	return func(services.getTypeConverter().getSeqLDT().getSeqEmpty());
    }
    
    
    public Term seqSingleton(S services, Term x) {
	return func(services.getTypeConverter().getSeqLDT().getSeqSingleton(), 
		    x);
    }
    
    
    public Term seqConcat(S services, Term s, Term s2) {
	return func(services.getTypeConverter().getSeqLDT().getSeqConcat(), 
		    s, 
		    s2);
    }
    
    
    public Term seqSub(S services, Term s, Term from, Term to) {
	return func(services.getTypeConverter().getSeqLDT().getSeqSub(), 
		    new Term[]{s, from, to});
    }
    
    
    public Term seqReverse(S services, Term s) {
	return func(services.getTypeConverter().getSeqLDT().getSeqReverse(), s);
    }

    //-------------------------------------------------------------------------
    // misc    (moved from key.util.MiscTools)
    //-------------------------------------------------------------------------


    public ImmutableSet<Term> unionToSet(Term s, S services) {
    final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
    assert s.sort().equals(setLDT.targetSort());
    final Function union = setLDT.getUnion();
    ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        ImmutableList<Term> workingList = ImmutableSLList.<Term>nil().prepend(s);
        while(!workingList.isEmpty()) {
            Term f = workingList.head();
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
    public Term goBelowUpdates(Term term) {
        while(term.op() instanceof UpdateApplication) {
            term = UpdateApplication.getTarget(term);
        }
        return term;
    }



    /**
     * Removes leading updates from the passed term.
     */
    public Pair<ImmutableList<Term>,Term> goBelowUpdates2(Term term) {
    ImmutableList<Term> updates = ImmutableSLList.<Term>nil();
        while(term.op() instanceof UpdateApplication) {
            updates = updates.append(UpdateApplication.getUpdate(term));
            term = UpdateApplication.getTarget(term);
        }
        return new Pair<ImmutableList<Term>,Term>(updates, term);
    }



    public Term seqDef(QuantifiableVariable qv,
                       Term a,
                       Term b,
                       Term t,
                       IServices services) {
        return func(services.getTypeConverter().getSeqLDT().getSeqDef(),
                    new Term[]{a, b, t},
                    new ImmutableArray<QuantifiableVariable>(qv));
    }

    public Term values(IServices services){
    	return func(services.getTypeConverter().getSeqLDT().getValues());
    }

    /**
      * Returns the {@link Sort}s of the given {@link Term}s.
      * @param terms The given {@link Term}s.
      * @return The {@link Term} {@link Sort}s.
      */
    public ImmutableList<Sort> getSorts(Iterable<Term> terms) {
       ImmutableList<Sort> result = ImmutableSLList.<Sort>nil();
       for (Term t : terms) {
          result = result.append(t.sort());
       }
       return result;
    }


}
