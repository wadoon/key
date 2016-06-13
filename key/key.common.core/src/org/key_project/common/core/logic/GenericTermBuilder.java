package org.key_project.common.core.logic;

import java.util.Map;

import org.key_project.common.core.logic.label.TermLabel;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.LogicVariable;
import org.key_project.common.core.logic.op.ParsableVariable;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.SchemaVariable;
import org.key_project.common.core.logic.op.UpdateableOperator;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.program.GenericNameAbstractionTable;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * 
 * TODO: Document.
 *
 * @author Dominic Scheurer
 *
 * @param <S>
 * @param <T>
 * @param <V>
 * @param <N>
 * @param <P>
 */
public interface GenericTermBuilder<S, N extends GenericNameAbstractionTable<S>, P extends ModalContent<S, N>, V extends Visitor<S, N, V, T>, T extends GenericTerm<S, N, V, T>> {

    public abstract T eqAtLocsPost(TermServices<S, N, P, V, T> services, T heap1_pre, T heap1_post,
            T locset1, T heap2_pre, T heap2_post, T locset2);

    public abstract T eqAtLocs(TermServices<S, N, P, V, T> services, T heap1, T locset1,
            T heap2, T locset2);

    public abstract T orPreserveLabels(T t1, T t2);

    public abstract T orPreserveLabels(Iterable<T> subTerms);

    public abstract T andPreserveLabels(T t1, T t2);

    public abstract T andPreserveLabels(Iterable<T> subTerms);

    public abstract T notPreserveLabels(T t);

    public abstract T impPreserveLabels(T t1, T t2);

    public abstract ImmutableList<Sort> getSorts(Iterable<T> terms);

    public abstract T values();

    public abstract T seqDef(QuantifiableVariable qv, T a, T b,
            T t);

//    public static abstract Pair<ImmutableList<T>,T> goBelowUpdates2(T term);

//    public static abstract T goBelowUpdates(T term);

    public abstract ImmutableSet<T> unionToSet(T s);

    public abstract T seqReverse(T s);

    public abstract T seqSub(T s, T from, T to);

    public abstract T seq(ImmutableList<T> terms);

    public abstract T seq(@SuppressWarnings("unchecked") T... terms);

    public abstract T seqConcat(T s, T s2);

    public abstract T seqSingleton(T x);

    public abstract T seqEmpty();

    public abstract T indexOf(T s, T x);

    public abstract T seqLen(T s);

    public abstract T seqGet(Sort asSort, T s, T idx);

    public abstract T reach(T h, T s, T o1,
            T o2, T n);

    public abstract T acc(T h, T s, T o1,
            T o2);

    public abstract T forallHeaps(TermServices<S, N, P, V, T> services, T t);

//    public abstract T anonUpd(LocationVariable heap, T mod, T anonHeap);

    public abstract T frameStrictlyEmpty(T heapTerm, Map<T,T> normalToAtPre);

    public abstract T frame(T heapTerm, Map<T,T> normalToAtPre, T mod);

//    public abstract T reachableValue(ProgramVariable pv);

//    public abstract T reachableValue(T t, KeYJavaType kjt);

//    public abstract T reachableValue(T h, T t, KeYJavaType kjt);

    public abstract T arrayStore(T o, T i, T v);

    public abstract T staticFieldStore(Function f, T v);

    public abstract T fieldStore(TermServices<S, N, P, V, T> services, T o, Function f,
            T v);

    public abstract T anon(T h1, T s, T h2);

    public abstract T create(T h, T o);

    public abstract T store(T h, T o, T f,
            T v);

    public abstract T classErroneous(Sort classSort);

    public abstract T classInitializationInProgress(Sort classSort);

    public abstract T classInitialized(Sort classSort);

    public abstract T classPrepared(Sort classSort);

    public abstract T initialized(T o);

    public abstract T created(T o);

    public abstract T created(T h, T o);

    public abstract T dotLength(T a);

    public abstract T dotArr(T ref, T idx);

    public abstract T unlabelRecursive(T term);

    public abstract T unlabel(T term);

    public abstract T shortcut(T term);

    public abstract T label(T term, TermLabel label);

    public abstract T label(T term, ImmutableArray<TermLabel> labels);

    public abstract T addLabel(T term, TermLabel label);

    public abstract T addLabel(T term, ImmutableArray<TermLabel> labels);

    public abstract T arr(T idx);

    public abstract T staticDot(Sort asSort, Function f);

    public abstract T staticDot(Sort asSort, T f);

//    public abstract T dot(Sort asSort, T o, LocationVariable field);

    public abstract T dot(Sort asSort, T o, Function f);

    public abstract T getBaseHeap();

    public abstract T dot(Sort asSort, T o, T f);

//    public abstract T select(Sort asSort, T h, T o,
//            LocationVariable field);

    public abstract T select(Sort asSort, T h, T o,
            T f);

//    public abstract T staticInv(KeYJavaType t);

//    public abstract T staticInv(T[] h, KeYJavaType t);

    public abstract T inv(T o);

    public abstract T inv(T[] h, T o);

//    public abstract T permissionsFor(LocationVariable permHeap, LocationVariable regularHeap);

    public abstract T permissionsFor(T permHeap, T regularHeap);

//    public abstract T wellFormed(LocationVariable heap);

    public abstract T wellFormed(T heap);

    public abstract T deepNonNull(T o, T d);

    public abstract T NULL();

    public abstract T[] wd(T[] l);

    public abstract ImmutableList<T> wd(Iterable<T> l);

    public abstract T wd(T t);

    public abstract T createdLocs();

    public abstract T createdInHeap(T s, T h);

    public abstract T disjoint(T s1, T s2);

    public abstract T subset(T s1, T s2);

    public abstract T elementOf(T o, T f, T s);

    public abstract T freshLocs(T h);

    public abstract T arrayRange(T o, T lower, T upper);

    public abstract T allObjects(T f);

    public abstract T allFields(T o);

    public abstract T setComprehension(QuantifiableVariable[] qvs, T guard,
            T o, T f);

    public abstract T setComprehension(QuantifiableVariable[] qvs, T o,
            T f);

    public abstract T infiniteUnion(QuantifiableVariable[] qvs, T guard, T s);

    public abstract T infiniteUnion(QuantifiableVariable[] qvs, T s);

    public abstract T setMinus(T s1, T s2);

    public abstract T intersect(Iterable<T> subTerms);

    public abstract T intersect(@SuppressWarnings("unchecked") T ... subTerms);

    public abstract T intersect(T s1, T s2);

    public abstract T union(Iterable<T> subTerms);

    public abstract T union(@SuppressWarnings("unchecked") T ... subTerms);

    public abstract T union(T s1, T s2);

    public abstract T singleton(T o, T f);

    public abstract T allLocs();

    public abstract T empty();

    public abstract T strictlyNothing();

    public abstract T index();

    public abstract T inLong(T var);

    public abstract T inInt(T var);

    public abstract T inChar(T var);

    public abstract T inShort(T var);

    public abstract T inByte(T var);

    public abstract T add(T t1, T t2);

    public abstract T zTerm(long number);

    public abstract T zTerm(String numberString);

    public abstract T one();

    public abstract T zero();

    public abstract T leq(T t1, T t2);

    public abstract T lt(T t1, T t2);

    public abstract T gt(T t1, T t2);

    public abstract T geq(T t1, T t2);

    public abstract T FALSE();

    public abstract T TRUE();

//    public abstract T applyUpdatePairsSequential(ImmutableList<UpdateLabelPair> updates, T target);

    public abstract T applySequential(ImmutableList<T> updates, T target);

    public abstract T applySequential(T[] updates, T target);

    public abstract T applyParallel(T[] lhss, T[] values, T target);

    public abstract T applyParallel(ImmutableList<T> updates, T target);

    public abstract T applyParallel(T[] updates, T target);

    public abstract ImmutableList<T> applyElementary(T heap, Iterable<T> targets);

    public abstract T applyElementary(T heap, T target);

    public abstract T applyElementary(T loc, T value,
            T target);

    public abstract T apply(T update, T target, ImmutableArray<TermLabel> labels);

    public abstract ImmutableList<T> apply(T update, ImmutableList<T> targets);

    public abstract T apply(T update, T target);

    public abstract T sequential(ImmutableList<T> updates);

    public abstract T sequential(T[] updates);

    public abstract T sequential(T u1, T u2);

    public abstract T parallel(Iterable<T> lhss, Iterable<T> values);

    public abstract T parallel(T[] lhss, T[] values);

    public abstract T parallel(ImmutableList<T> updates);

    public abstract T parallel(@SuppressWarnings("unchecked") T... updates);

    public abstract T parallel(T u1, T u2);

    public abstract T skip();

    public abstract T elementary(T lhs, T rhs);

    public abstract T elementary(UpdateableOperator lhs, T rhs);

    public abstract T convertToBoolean(T a);

    public abstract T convertToFormula(T a);

    public abstract T measuredByEmpty();

    public abstract Function getMeasuredByEmpty();

    public abstract T measuredBy(T mby);

    public abstract T measuredByCheck(T mby);

    public abstract T prec(T mby, T mbyAtPre);

    public abstract T pair(T first, T second);

    public abstract T exactInstance(Sort s, T t);

    public abstract T instance(Sort s, T t);

    public abstract T subst(QuantifiableVariable substVar, T substTerm, T origTerm);

    //TODO (DS) Will probably need that definitely!!!
//    public abstract T subst(SubstOp op, QuantifiableVariable substVar, T substTerm,
//            T origTerm);

    public abstract T equals(T t1, T t2);

    public abstract T imp(T t1, T t2, ImmutableArray<TermLabel> labels);

    public abstract T imp(T t1, T t2);

    public abstract T orSC(Iterable<T> subTerms);

    public abstract T or(Iterable<T> subTerms);

    public abstract T orSC(@SuppressWarnings("unchecked") T... subTerms);

    public abstract T or(@SuppressWarnings("unchecked") T... subTerms);

    public abstract T orSC(T t1, T t2);

    public abstract T or(T t1, T t2);

    public abstract T andSC(Iterable<T> subTerms);

    public abstract T and(Iterable<T> subTerms);

    public abstract T andSC(@SuppressWarnings("unchecked") T ... subTerms);

    public abstract T and(@SuppressWarnings("unchecked") T ... subTerms);

    public abstract T andSC(T t1, T t2);

    public abstract T and(T t1, T t2);

    public abstract T not(T t);

    public abstract T max(ImmutableList<QuantifiableVariable> qvs, T range, T t,
            TermServices<S, N, P, V, T> services);

    public abstract T min(ImmutableList<QuantifiableVariable> qvs, T range, T t,
            TermServices<S, N, P, V, T> services);

    public abstract T prod(ImmutableList<QuantifiableVariable> qvs, T range, T t,
            TermServices<S, N, P, V, T> services);

    public abstract T bprod(QuantifiableVariable qv, T a, T b,
            T t, TermServices<S, N, P, V, T> services);

    public abstract T sum(ImmutableList<QuantifiableVariable> qvs, T range, T t);

    public abstract T bsum(QuantifiableVariable qv, T a, T b,
            T t);

    public abstract T ex(Iterable<QuantifiableVariable> qvs, T t);

    public abstract T ex(QuantifiableVariable qv, T t);

    public abstract T open(T formula);

    public abstract T allClose(T t);

    public abstract T all(Iterable<QuantifiableVariable> qvs, T t);

    public abstract T all(QuantifiableVariable qv, T t);

    public abstract T ff();

    public abstract T tt();

    public abstract T cast(Sort s, T t);

    public abstract T ifEx(ImmutableList<QuantifiableVariable> qvs, T cond, T _then,
            T _else);

    public abstract T ifEx(QuantifiableVariable qv, T cond, T _then,
            T _else);

    public abstract T ife(T cond, T _then, T _else);

    public abstract T dia(P jb, T t);

    public abstract T box(P jb, T t);

//    public abstract T prog(Modality mod, P jb, T t,
//            ImmutableArray<TermLabel> labels);

//    public abstract T prog(Modality mod, P jb, T t);

    public abstract T func(Function f, T[] s, ImmutableArray<QuantifiableVariable> boundVars);

//    public abstract T func(IObserverFunction f, T ... s);

    public abstract T func(Function f, @SuppressWarnings("unchecked") T ... s);

    public abstract T func(Function f, T s1, T s2);

    public abstract T func(Function f, T s);

    public abstract T func(Function f);

    public abstract T var(ParsableVariable v);

    public abstract T var(SchemaVariable v);

//    public abstract ImmutableList<T> var(Iterable<ProgramVariable> vs);

//    public abstract ImmutableList<T> var(ProgramVariable ... vs);

//    public abstract T var(ProgramVariable v);

    public abstract T var(LogicVariable v);

//    public abstract LocationVariable heapAtPreVar(String baseName, Sort sort, boolean makeNameUnique);

//    public abstract LocationVariable heapAtPreVar(String baseName, boolean makeNameUnique);

//    public abstract LocationVariable excVar(String name, IProgramMethod pm, boolean makeNameUnique);

//    public abstract LocationVariable excVar(IProgramMethod pm, boolean makeNameUnique);

//    public abstract LocationVariable resultVar(String name, IProgramMethod pm, boolean makeNameUnique);

//    public abstract LocationVariable resultVar(IProgramMethod pm, boolean makeNameUnique);

//    public abstract ImmutableList<ProgramVariable> paramVars(String postfix, IObserverFunction obs, boolean makeNamesUnique);

//    public abstract ImmutableList<ProgramVariable> paramVars(IObserverFunction obs, boolean makeNamesUnique);

//    public abstract LocationVariable selfVar(IProgramMethod pm, KeYJavaType kjt, boolean makeNameUnique);

//    public abstract LocationVariable selfVar(IProgramMethod pm, KeYJavaType kjt, boolean makeNameUnique,
//            String postfix);

//    public abstract LocationVariable selfVar(KeYJavaType kjt, boolean makeNameUnique, String postfix);

//    public abstract LocationVariable selfVar(KeYJavaType kjt, boolean makeNameUnique);

    public abstract String newName(Sort sort);

    public abstract String newName(String baseName);

    public abstract String shortBaseName(Sort s);

//    public abstract T parseTerm(String s, NamespaceSet namespaces)
//            throws ParserException;

//    public abstract T parseTerm(String s) throws ParserException;

    public abstract GenericTermFactory<S, N, P, V, T> tf();

}
