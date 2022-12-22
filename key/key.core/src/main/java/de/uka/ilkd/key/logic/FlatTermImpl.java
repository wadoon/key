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

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.logic.op.*;
import org.key_project.util.collection.*;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.sort.Sort;

import javax.annotation.Nullable;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;


/**
 * The currently only class implementing the Term interface. FlatTermFactory should
 * be the only class dealing directly with the FLatTermImpl class.
 */
public class FlatTermImpl implements Term {


    private static final ImmutableArray<TermLabel> EMPTY_LABEL_LIST
            = new ImmutableArray<TermLabel>();


    /**
     * A static empty list of quantifiable variables used for memory reasons.
     */
    private static final ImmutableArray<QuantifiableVariable> EMPTY_VAR_LIST
            = new ImmutableArray<>();



    private static AtomicInteger serialNumberCounter = new AtomicInteger();
    private final int serialNumber = serialNumberCounter.incrementAndGet();

    //caches
    static enum ThreeValuedTruth { TRUE, FALSE, UNKNOWN }

    private int depth = -1;
    /**
     * A cached value for computing the term's rigidness.
     */
    private ThreeValuedTruth rigid = ThreeValuedTruth.UNKNOWN;
    private ImmutableSet<QuantifiableVariable> freeVars = null;
    private int hashcode = -1;



    private  ImmutableArray<Operator> symbols;

    private  ImmutableArray<Integer> ends;

    private   ImmutableArray<ImmutableArray<QuantifiableVariable>> boundVars ;

    private  ImmutableArray<JavaBlock> javaBlocks ;

    /**
     * This flag indicates that the {@link Term} itself or one
     * of its children contains a non empty {@link JavaBlock}.
     * {@link Term}s which provides a {@link JavaBlock} directly or indirectly
     * can't be cached because it is possible that the contained meta information
     * inside the {@link JavaBlock}, e.g. {@link PositionInfo}s, are different.
     */
    private ThreeValuedTruth containsJavaBlockRecursive = ThreeValuedTruth.UNKNOWN;

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------


    public FlatTermImpl(ImmutableArray<Operator> symbols,
                        ImmutableArray<Integer> ends,
                        ImmutableArray<ImmutableArray<QuantifiableVariable>> boundVars,
                        ImmutableArray<JavaBlock> javaBlocks) {
        assert symbols != null;
        assert ends != null;
        this.symbols =  symbols;
        this.ends = ends ;
        this.boundVars =  boundVars;
        this.javaBlocks = javaBlocks ;
    }


    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------

    /**
     *
     * */

    public static <T> T[] range(Class<T> clazz,ImmutableArray<T> array, int start, int end) {
        @SuppressWarnings("unchecked")
        T[] res = (T[]) Array.newInstance(clazz, end-start + 1);
        for(int x = 0; x <= end-start; x++){
            res[x] = array.get(x+start);
        }
        return res ;
    }

    /**
     *
     * */
    private int findSubtermStartIndex(int n){
        if(n == 0 || n == 1){
            return n ;
        }
        int res = 1 ;
        for(int index = 0 ; index < n - 1 ; index++){
            res = ends.get(res) + 1;
        }
        return res ;
    }

    /**
     *
     * */
    private int findSubtermEndIndex(int subtermStartIndex){
        return ends.get(subtermStartIndex);
    }

    /**
     *
     * */
    private  Integer[] updateSubsEndIndexs(Integer[] ends ,int startIndex){
        for(int i = 0 ; i < ends.length ; i++){
            ends[i] = ends[i] - startIndex ;
        }
        return ends ;
    }

    private ImmutableSet<QuantifiableVariable> determineFreeVars() {

        ImmutableSet<QuantifiableVariable> localFreeVars =  DefaultImmutableSet.<QuantifiableVariable>nil();
        Operator op = op();

        if(op instanceof QuantifiableVariable) {
            localFreeVars = localFreeVars.add((QuantifiableVariable) op);
        }
        for(int i = 0, ar = arity(); i < ar; i++) {
            ImmutableSet<QuantifiableVariable> subFreeVars = sub(i).freeVars();

            //----------------------------------------------------------
            for(int j = 0, sz = varsBoundHere(i).size(); j < sz; j++) {
                subFreeVars = subFreeVars.remove(varsBoundHere(i).get(j));
            }

            localFreeVars = localFreeVars.union(subFreeVars);
        }
        return localFreeVars;
    }


    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    /**
     * Checks whether the Term is valid on the top level. If this is
     * the case this method returns the Term unmodified. Otherwise a
     * TermCreationException is thrown.
     */
    public Term checked() {
        symbols.get(0).validTopLevelException(this);
        return this;
        /*if (op.validTopLevel(this)) {
            return this;
        } else {
            throw new TermCreationException(op, this);
        }*/
    }


    public ImmutableArray<Operator> symbols(){
        return  symbols;
    }

    public ImmutableArray<Integer> ends() {
        return ends;
    }

    public ImmutableArray<JavaBlock> javaBlocks() {
        return javaBlocks;
    }


    public  ImmutableArray<QuantifiableVariable> boundVars(int i){
        if(boundVars == null || boundVars.get(i) == null){ return EMPTY_VAR_LIST ;}
        return boundVars.get(i) ;
    }

        @Override
    public Operator op() {
        return this.symbols.get(0);
    }

    @Override
    public <T> T op(Class<T> opClass)
            throws IllegalArgumentException {
        if (!opClass.isInstance(symbols.get(0))) {
            throw new IllegalArgumentException(
                    "Operator does not match the expected type:\n"
                            + "Operator type was: " + symbols.get(0).getClass() + "\n"
                            + "Expected type was: " + opClass);
        }
        return opClass.cast(symbols.get(0));
    }

    @Override
    public ImmutableArray<Term> subs() {
        Term[] res = new Term[symbols.get(0).arity()];
        for(int i = 0 ; i < symbols.get(0).arity() ; i++){
            res[i] = sub(i);
        }
        return new ImmutableArray<>(res);
    }

    @Override
    public Term sub(int n) {

        int start;
        int end;
        start =  findSubtermStartIndex(n + 1);
        end   =  findSubtermEndIndex(start);
        
        Integer[] subEnds = updateSubsEndIndexs(range(Integer.class,ends,start,end),start);
        Operator[] subSymbols = range(Operator.class,symbols,start,end);
        ImmutableArray<QuantifiableVariable>[] subBoundVars = new ImmutableArray[end - start + 1];
        JavaBlock[] subJavaBlock = range(JavaBlock.class,javaBlocks,start,end);

        for(int i = start, x = 0 ; i <= end ; i++ , x++){
            subBoundVars[x] = boundVars(i);
        }
        return  new FlatTermImpl( new ImmutableArray<>(subSymbols)
                                 ,new ImmutableArray<>(subEnds)
                                 ,new ImmutableArray<>(subBoundVars)
                                 ,new ImmutableArray<>(subJavaBlock));
    }

    @Override
    public ImmutableArray<QuantifiableVariable> boundVars(){
        if(boundVars == null || boundVars.get(0) == null) return EMPTY_VAR_LIST ;
        return boundVars.get(0);
    }

    @Override
    public ImmutableArray<QuantifiableVariable> varsBoundHere(int n) {
        return op().bindVarsAt(n) ? this.boundVars() : EMPTY_VAR_LIST ;
    }

    @Override
    public JavaBlock javaBlock() {
        if(javaBlocks == null || javaBlocks.get(0) == null ) return JavaBlock.EMPTY_JAVABLOCK ;
        return javaBlocks.get(0);
    }

    @Override
    public int arity() {
        return this.symbols.get(0).arity();
    }

    @Override
    public Sort sort() {
        //return op.sort(subs);
        return symbols.get(0).sort(subs());
    }

    @Override
    public int depth() {
        if(depth == -1) {
            int localDepth = -1;
            for (int i = 0, n = arity(); i < n; i++) {
                final int subTermDepth = sub(i).depth();
                if(subTermDepth > depth) {
                    localDepth = subTermDepth;
                }
            }
            ++localDepth;
            depth = localDepth;
        }
        return depth;
    }

    public int flatDepth() {
        if(depth == -1) {
            int localDepth = -1;
            for (int i = 0, n = arity(); i < n; i++) {
                final int subTermDepth =  (findSubtermEndIndex(findSubtermStartIndex(i)) - findSubtermStartIndex(i));
                if(subTermDepth > depth) {
                    localDepth = subTermDepth;
                }
            }
        }
        return depth;
    }



    @Override
    public boolean isRigid() {
        if(rigid == ThreeValuedTruth.UNKNOWN) {
            if(!op().isRigid()) {
                rigid = ThreeValuedTruth.FALSE;
            } else {
                ThreeValuedTruth localIsRigid = ThreeValuedTruth.TRUE;
                for(int i = 0, n = arity(); i < n; i++) {
                    if(!sub(i).isRigid()) {
                        localIsRigid = ThreeValuedTruth.FALSE;
                        break;
                    }
                }
                rigid = localIsRigid;
            }
        }

        return rigid == ThreeValuedTruth.TRUE;
    }

    @Override
    public ImmutableSet<QuantifiableVariable> freeVars() {
        if(freeVars == null) {
           freeVars = determineFreeVars();
        }
        return freeVars;
    }


    @Override
    public void execPostOrder(Visitor visitor) {
        visitor.subtreeEntered(this);
        if (visitor.visitSubtree(this)) {
            for(int i = 0, ar = arity(); i < ar; i++) {
                sub(i).execPostOrder(visitor);
            }
        }
        visitor.visit(this);
        visitor.subtreeLeft(this);
    }


    @Override
    public void execPreOrder(Visitor visitor) {
        visitor.subtreeEntered(this);
        visitor.visit(this);
        if (visitor.visitSubtree(this)) {
            for (int i = 0, ar = arity(); i < ar; i++) {
                sub(i).execPreOrder(visitor);
            }
        }
        visitor.subtreeLeft(this);
    }

    @Override
    public boolean equalsModRenaming(Term o) {
        if(o == this) {
            return true;
        }
        return unifyHelp(this, o,
                ImmutableSLList.<QuantifiableVariable>nil(),
                ImmutableSLList.<QuantifiableVariable>nil(),
                null);
    }

    //
    // equals modulo renaming logic


    /**
     * compare two quantifiable variables if they are equal modulo renaming
     *
     * @param ownVar
     *            first QuantifiableVariable to be compared
     * @param cmpVar
     *            second QuantifiableVariable to be compared
     * @param ownBoundVars
     *            variables bound above the current position
     * @param cmpBoundVars
     *            variables bound above the current position
     */
    private static boolean compareBoundVariables(QuantifiableVariable ownVar,
                                                 QuantifiableVariable cmpVar,
                                                 ImmutableList<QuantifiableVariable> ownBoundVars,
                                                 ImmutableList<QuantifiableVariable> cmpBoundVars) {

        final int ownNum = indexOf(ownVar, ownBoundVars);
        final int cmpNum = indexOf(cmpVar, cmpBoundVars);

        if (ownNum == -1 && cmpNum == -1) {
            // if both variables are not bound the variables have to be the
            // same object
            return ownVar == cmpVar;
        }

        // otherwise the variables have to be bound at the same point (and both
        // be bound)
        return ownNum == cmpNum;
    }

    /**
     * @return the index of the first occurrence of <code>var</code> in
     *         <code>list</code>, or <code>-1</code> if the variable is not an
     *         element of the list
     */
    private static int indexOf(QuantifiableVariable var,
                               ImmutableList<QuantifiableVariable> list) {
        int res = 0;
        while (!list.isEmpty()) {
            if (list.head() == var) {
                return res;
            }
            ++res;
            list = list.tail();
        }
        return -1;
    }


    private boolean unifyHelp(Term t0, Term t1,
                              ImmutableList<QuantifiableVariable> ownBoundVars,
                              ImmutableList<QuantifiableVariable> cmpBoundVars,
                              NameAbstractionTable nat) {

        if (t0 == t1 && ownBoundVars.equals(cmpBoundVars)) {
            return true;
        }

        final Operator op0 = t0.op();

        if (op0 instanceof QuantifiableVariable) {
            return handleQuantifiableVariable(t0, t1, ownBoundVars,
                    cmpBoundVars);
        }

        final Operator op1 = t1.op();

        if (!(op0 instanceof ProgramVariable) && op0 != op1) {
            return false;
        }

        if (t0.sort() != t1.sort() || t0.arity() != t1.arity()) {
            return false;
        }

        nat = handleJava(t0, t1, nat);
        if (nat == FAILED) {
            return false;
        }

        return descendRecursively(t0, t1, ownBoundVars, cmpBoundVars, nat);
    }

    private boolean handleQuantifiableVariable(Term t0, Term t1,
                                               ImmutableList<QuantifiableVariable> ownBoundVars,
                                               ImmutableList<QuantifiableVariable> cmpBoundVars) {
        if (!((t1.op() instanceof QuantifiableVariable) && compareBoundVariables(
                (QuantifiableVariable) t0.op(), (QuantifiableVariable) t1.op(),
                ownBoundVars, cmpBoundVars))) {
            return false;
        }
        return true;
    }

    /**
     * used to encode that <tt>handleJava</tt> results in an unsatisfiable
     * constraint (faster than using exceptions)
     */
    private static NameAbstractionTable FAILED = new NameAbstractionTable();

    private static NameAbstractionTable handleJava(Term t0, Term t1,
                                                   NameAbstractionTable nat) {

        if (!t0.javaBlock().isEmpty() || !t1.javaBlock().isEmpty()) {
            nat = checkNat(nat);
            if (!t0.javaBlock().equalsModRenaming(t1.javaBlock(), nat)) {
                return FAILED;
            }
        }

        if (!(t0.op() instanceof SchemaVariable)
                && t0.op() instanceof ProgramVariable) {
            if (!(t1.op() instanceof ProgramVariable)) {
                return FAILED;
            }
            nat = checkNat(nat);
            if (!((ProgramVariable) t0.op()).equalsModRenaming(
                    (ProgramVariable) t1.op(), nat)) {
                return FAILED;
            }
        }

        return nat;
    }


    private boolean descendRecursively(Term t0, Term t1,
                                       ImmutableList<QuantifiableVariable> ownBoundVars,
                                       ImmutableList<QuantifiableVariable> cmpBoundVars,
                                       NameAbstractionTable nat) {

        for (int i = 0; i < t0.arity(); i++) {
            ImmutableList<QuantifiableVariable> subOwnBoundVars = ownBoundVars;
            ImmutableList<QuantifiableVariable> subCmpBoundVars = cmpBoundVars;

            if (t0.varsBoundHere(i).size() != t1.varsBoundHere(i).size()) {
                return false;
            }
            for (int j = 0; j < t0.varsBoundHere(i).size(); j++) {
                final QuantifiableVariable ownVar = t0.varsBoundHere(i).get(j);
                final QuantifiableVariable cmpVar = t1.varsBoundHere(i).get(j);
                if (ownVar.sort() != cmpVar.sort()) {
                    return false;
                }

                subOwnBoundVars = subOwnBoundVars.prepend(ownVar);
                subCmpBoundVars = subCmpBoundVars.prepend(cmpVar);
            }

            boolean newConstraint = unifyHelp(t0.sub(i), t1.sub(i),
                    subOwnBoundVars, subCmpBoundVars, nat);

            if (!newConstraint) {
                return false;
            }
        }

        return true;
    }

    private static NameAbstractionTable checkNat(NameAbstractionTable nat) {
        if (nat == null) {
            return new NameAbstractionTable();
        }
        return nat;
    }

    //
    // end of equals modulo renaming logic


    /**
     * true iff <code>o</code> is syntactically equal to this term
     */
    @Override
    public boolean equals(Object o) {
        if(o == this) {
            return true;
        }

        if(o == null || o.getClass() != getClass()
                || hashCode() != o.hashCode()) {
            return false;
        }

        final FlatTermImpl t = (FlatTermImpl) o;
        Operator op = op();

        return op.equals(t.op())
                && t.hasLabels() == hasLabels()
                && subs().equals(t.subs())
                && boundVars(0).equals(t.boundVars(0))
                && javaBlock().equals(t.javaBlock());
    }

    @Override
    public boolean equalsModIrrelevantTermLabels(Object o) {
        if(o == this) {
            return true;
        }

        if(o == null || !(o instanceof FlatTermImpl)) {
            return false;
        }

        final FlatTermImpl t = (FlatTermImpl) o;

        if (!(op().equals(t.op())
                && boundVars(0).equals(t.boundVars(0))
                && javaBlock().equals(t.javaBlock()))) {
            return false;
        }

        Term other = (Term) o;

        for (TermLabel label : getLabels()) {
            if (label.isProofRelevant() && !other.getLabels().contains(label)) {
                return false;
            }
        }

        for (TermLabel label : other.getLabels()) {
            if (label.isProofRelevant() && !getLabels().contains(label)) {
                return false;
            }
        }

        for (int i = 0; i < subs().size(); ++i) {
            if (!subs().get(i).equalsModIrrelevantTermLabels(t.subs().get(i))) {
                return false;
            }
        }

        return true;
    }

    @Override
    public boolean equalsModTermLabels(Object o) {
        if (o == this) {
            return true;
        }

        if (!(o instanceof TermImpl)) {
            return false;
        }

        final FlatTermImpl t = (FlatTermImpl) o;

        if (!(op().equals(t.op())
                && boundVars(0).equals(t.boundVars(0))
                && javaBlock().equals(t.javaBlock()))) {
            return false;
        }

        for (int i = 0; i < subs().size(); ++i) {
            if (!subs().get(i).equalsModTermLabels(t.subs().get(i))) {
                return false;
            }
        }
        return true;
    }

    @Override
    public final int hashCode(){
        if(hashcode == -1) {
            // compute into local variable first to be thread-safe.
            this.hashcode = computeHashCode();
        }
        return hashcode;
    }

    /**
     * Performs the actual computation of the hashcode and can be overwritten by subclasses
     * if necessary
     */
    protected int computeHashCode() {
        int hashcode = 5;
        hashcode = hashcode * 17 + op().hashCode();
        hashcode = hashcode * 17 + subs().hashCode();
        hashcode = hashcode * 17 + boundVars().hashCode();
        hashcode = hashcode * 17 + javaBlock().hashCode();

        if(hashcode == -1) {
            hashcode = 0;
        }
        return hashcode;
    }

    /**
     * returns a linearized textual representation of this term
     */
    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        JavaBlock javaBlock = javaBlock();
        ImmutableArray<QuantifiableVariable> boundvars = boundVars() ;

        if(!javaBlock.isEmpty()) {
            if(op() == Modality.DIA) {
                sb.append("\\<").append(javaBlock).append("\\> ");
            } else if (op() == Modality.BOX) {
                sb.append("\\[").append(javaBlock).append("\\] ");
            } else {
                sb.append(op()).append("\\[").append(javaBlock).append("\\] ");
            }
            sb.append("(").append(sub(0)).append(")");
            return sb.toString();
        } else {
            sb.append(op().name().toString());
            if(!boundvars.isEmpty()) {
                sb.append("{");
                for(int i = 0, n = boundvars.size(); i < n; i++) {
                    sb.append(boundvars.get(i));
                    if(i < n - 1) {
                        sb.append(", ");
                    }
                }
                sb.append("}");
            }
            if(arity() == 0) {
                return sb.toString();
            }
            sb.append("(");
            for(int i = 0, ar = arity(); i < ar; i++) {
                sb.append(sub(i));
                if(i < ar - 1) {
                    sb.append(",");
                }
            }
            sb.append(")");
        }

        return sb.toString();
    }

    @Override
    public int serialNumber() {
        return serialNumber;
    }

    @Override
    public boolean hasLabels() {
        return false;
    }

    @Override
    public boolean containsLabel(TermLabel label) {
        return false;
    }

    @Override
    public TermLabel getLabel(Name termLabelName) {
        return null;
    }

    @Override
    public ImmutableArray<TermLabel> getLabels() {
        return EMPTY_LABEL_LIST;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean containsJavaBlockRecursive() {
        if ( containsJavaBlockRecursive == ThreeValuedTruth.UNKNOWN ) {
            ThreeValuedTruth result = ThreeValuedTruth.FALSE;
            if (javaBlocks.get(0) != null && !javaBlocks.get(0).isEmpty() ) {
                result = ThreeValuedTruth.TRUE;
            } else {
                for (int i = 0, arity = subs().size(); i<arity; i++) {
                    if (subs().get(i).containsJavaBlockRecursive()) {
                        result = ThreeValuedTruth.TRUE;
                        break;
                    }
                }
            }
            this.containsJavaBlockRecursive = result;
        }
        return containsJavaBlockRecursive == ThreeValuedTruth.TRUE;
    }

    private String origin;

    @Override
    public @Nullable String getOrigin() {
        return origin;
    }

    public void setOrigin(String origin) {
        this.origin = origin;
    }
}
