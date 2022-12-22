package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nonnull;
import java.lang.reflect.Array;
import java.util.*;

public class FlatTermFactory extends  AbstractTermFactory{



    private static final ImmutableArray<Term> NO_SUBTERMS = new ImmutableArray<Term>();
    private final Map<Term, Term> cache;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------


    FlatTermFactory() {
        this.cache = null;
    }

    FlatTermFactory(Map<Term, Term> cache) {
        this.cache = cache;
    }

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------



    /**
     * Master method for term creation. Should be the only place where terms
     * are created in the entire system.
     */
    public Term createTerm(Operator op,
                           ImmutableArray<Term> subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock,
                           ImmutableArray<TermLabel> labels) {

        if(op == null) {
            throw new TermCreationException("Given operator is null.");
        }

        if (subs == null || subs.isEmpty()) {
            subs = NO_SUBTERMS;
        }

        return doCreateTerm(op, subs, boundVars, javaBlock, labels);
    }

    public Term createTerm(Operator op,
                           ImmutableArray<Term> subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock) {

        return createTerm(op, subs, boundVars, javaBlock, null);
    }


    public Term createTerm(Operator op,
                           Term[] subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock) {
        return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, null);
    }


    public Term createTerm(Operator op, Term... subs) {
        return createTerm(op, subs, null, null);
    }

    public Term createTerm(Operator op,
                           Term[] subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock,
                           ImmutableArray<TermLabel> labels) {
        return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, labels);
    }

    public Term createTerm(Operator op,
                           Term[] subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock,
                           TermLabel label) {
        return createTerm(op, createSubtermArray(subs), boundVars,
                javaBlock, new ImmutableArray<TermLabel>(label));
    }

    public Term createTerm(Operator op, Term[] subs, TermLabel label) {
        return createTerm(op, subs, null, null, label);
    }

    public Term createTerm(Operator op, Term[] subs, ImmutableArray<TermLabel> labels) {
        return createTerm(op, createSubtermArray(subs), null, null, labels);
    }

    public Term createTerm(Operator op, Term sub, ImmutableArray<TermLabel> labels) {
        return createTerm(op, new ImmutableArray<Term>(sub), null, null, labels);
    }

    public Term createTerm(Operator op, Term sub1, Term sub2, ImmutableArray<TermLabel> labels) {
        return createTerm(op, new Term[]{sub1, sub2}, null, null, labels);
    }


    public Term createTerm(Operator op, ImmutableArray<TermLabel> labels) {
        return createTerm(op, NO_SUBTERMS, null, null, labels);
    }

    //-------------------------------------------------------------------------
    //private interface
    //-------------------------------------------------------------------------

    private ImmutableArray<Term> createSubtermArray(Term[] subs) {
        return subs == null || subs.length == 0 ?
                NO_SUBTERMS : new ImmutableArray<Term>(subs);
    }
/**
    private void doCreateTermSymbols(Term sub, List<Operator> symbols){
        //
        if(sub.subs().isEmpty()){
            symbols.add(sub.op());
            return;
        }
        //
        symbols.add(sub.op());
        //
        for(int i = 0 ; i < sub.op().arity(); i++){
            doCreateTermSymbols(sub.sub(i),symbols);
        }
    }

    private  void  doCreateSymbolsArity(Term sub, List<Integer> arity ){
        //
        if(sub.subs().isEmpty()){
            arity.add(sub.op().arity());
            return;
        }
        //
        arity.add(sub.op().arity());
        //
        for(int i = 0 ; i < sub.op().arity(); i++){
            doCreateSymbolsArity(sub.sub(i),arity);
        }
    }

    private  List<Integer> doCreateEnds(List<Integer> arity){
        if(arity.size() == 1){
            return arity ;
        }
        int steps;
        int end = 0 ;
        for(int index = 0 ; index < arity.size() ; index++){

            steps = arity.get(index);
            end = index ;

            while(steps > 0){
                if(arity.get(end + 1) != 0){
                    steps = steps + arity.get(end + 1) - 1 ;
                }else{
                    steps = steps - 1 ;
                }
                end++ ;
            }
            arity.set(index ,end);
        }
        return  arity ;
    }

 */
    private Term doCreateTerm(Operator op, ImmutableArray<Term> subs,
                              ImmutableArray<QuantifiableVariable> boundVars,
                              JavaBlock javaBlock, ImmutableArray<TermLabel> labels) {

        int newTermSymbolsEndsLength = 1 ;
        // find the length of symbols and ends for the new Flatterm
        for(int i = 0 ; i < op.arity() ; i++){
            FlatTermImpl subFlatTerm = (FlatTermImpl)subs.get(i);
            newTermSymbolsEndsLength = newTermSymbolsEndsLength + subFlatTerm.symbols().size();
        }
        // create Operator and Integer array for the symbols and ends respectively
        Operator[] symbols = new Operator[newTermSymbolsEndsLength];
        Integer[] ends = new Integer[newTermSymbolsEndsLength];
        JavaBlock[] javaBlocks = new JavaBlock[newTermSymbolsEndsLength];
        ImmutableArray<QuantifiableVariable>[] boundVarsArray = new ImmutableArray[newTermSymbolsEndsLength];

        // the op added at the first postion
        symbols[0] = op ;
        javaBlocks[0] = javaBlock;
        boundVarsArray[0] = boundVars ;
        // the end of the op is the last index of the ends
        ends[0] = newTermSymbolsEndsLength - 1;

        // index ist to iterate in the array symbols and ends from index 1 to index symbols.length - 1(last index in symbols)
        int index = 1 ;
        // endSchift is needed to calculate the shifted ends of the subs
        int endsShift = index ;

        //number the subs is equal to the arity of the op
        for(int i = 0;i < op.arity() ; i++){
            //we assume that the Term is a FlatTerm so we cast the Term to use the symbols() and ends() methodes
            //and we start with the first subs (subs 0)
            FlatTermImpl subFlatTerm = (FlatTermImpl)subs.get(i);
            //we copy all of the symbols and ends in the i Flatterm to the symbols and ends, where the ends are modified
            for(int j = 0 ;  j < subFlatTerm.symbols().size(); j++){
                symbols[index] = subFlatTerm.symbols().get(j);
                ends[index] = subFlatTerm.ends().get(j) + endsShift;
                boundVarsArray[index] =  subFlatTerm.boundVars(j);
                javaBlocks[index] = subFlatTerm.javaBlocks().get(j);
                index++;
            }
            endsShift = index;;
        }

        return  new FlatTermImpl(new ImmutableArray<>(symbols), new ImmutableArray<>(ends),new ImmutableArray<>(boundVarsArray),new ImmutableArray<>(javaBlocks)).checked() ;
    }

    /**
     * Reduce the given list of terms into a one term by using the operator.
     * The reduction is left-associative. e.g., the result is
     * {@code ((a op b) op c) op d }.
     *
     * @param junctor the left-associative operator to combine the terms together
     * @param terms a list of non-null temrs
     */
    public @Nonnull Term createTerm(@Nonnull  Operator junctor, @Nonnull List<Term> terms) {
        if(terms.size()==1)
            return terms.get(0);
        else if (terms.size() == 2)
            return createTerm(junctor, terms.get(0), terms.get(1));
        final Optional<Term> reduce = terms.stream()
                .reduce((a, b) -> createTerm(junctor, a, b));
        if(reduce.isPresent())
            return reduce.get();
        throw new IllegalArgumentException("list of terms is empty.");
    }
}