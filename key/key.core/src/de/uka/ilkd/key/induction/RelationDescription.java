package de.uka.ilkd.key.induction;

import java.util.HashMap;
import java.util.LinkedList;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;

public class RelationDescription {

	private LinkedList<AtomicRelationDescription> atomics;
	private LinkedList<Pair<QuantifiableVariable, Term>> possibleSubstitutions;
	private Term term;
	private static final String COUNTER_NAME = "replacement_counter";
	
	/**
	 * @use RelationDescriptionFactory to generate
	 * @param t
	 * @param serv
	 */
	protected RelationDescription(Term t, Services serv){
		ConstructorExtractor ce = new ConstructorExtractor(t, serv);
		ImmutableArray<Function> constructors = ce.getConstructors();
		Iterable<Taclet> findTerms;
		
		this.term = t;
		
		possibleSubstitutions = new LinkedList<Pair<QuantifiableVariable, Term>>();
		
		//System.out.println("The term: " + t + " has " + constructors.size() + " constructors.");
		
		//TODO: check for cast error
		findTerms = serv.getProof().getInitConfig().activatedTaclets();
		
		atomics = createAtomics(findTerms, t, constructors, possibleSubstitutions, serv);
	}
	
	public LinkedList<AtomicRelationDescription> getAtomics(){
		return this.atomics;
	}
	
	
	/**
	 * 
	 * @param term
	 * @param findTerm
	 * @return if the findTerm is an instance of the given term this function returns a term which shows under 
	 * which condition the term would be the same as the findTerm. E.g. term = f(a), findTerm = f(g(x)) this function
	 * would return a = g(x). 
	 */
	private static Term createRangeFormula(Term term, Term findTerm, Services s){
		TermBuilder tb = s.getTermBuilder();
		
		if(term.arity() > 0 && findTerm.arity() > 0 && findTerm.op() == term.op()){
			LinkedList<Term> subterms = new LinkedList<>();
			for(int i = 0; i < term.arity(); i++){
				subterms.add(createRangeFormula(term.sub(i), findTerm.sub(i), s));
			}
			return tb.and(subterms);
		}
		else{
			//TODO:[optional] Maybe check arity for negative values and their handling
			
			if(!term.sort().equals(findTerm.sort())){	//TODO: take a closer look at this
				return tb.ff();
			}
			else{
				//TODO: replace all TermSV's with VariableSV in the findterm.
				findTerm = replaceTermSVwithVariableSV(findTerm, s, new HashMap<TermSV, QuantifiableVariable>());
				return tb.equals(term, findTerm);
			}
		}
		
	}
	

	public static Term replaceTermSVwithVariableSV(Term term, Services s, HashMap<TermSV, QuantifiableVariable> replace) {
		Operator op = term.op();
		TermBuilder tb = s.getTermBuilder();
		if(op instanceof TermSV){
			TermSV tsv = (TermSV)op;
			QuantifiableVariable replacedVar;
			if(replace.containsKey(tsv)){
				replacedVar = replace.get(tsv);
			}else {
				replacedVar = SchemaVariableFactory.createVariableSV(generateName(s, "replaced_"), term.sort());
				replace.put(tsv, replacedVar);
			}
			return tb.var(replacedVar);
		}
		else{
			if(op instanceof Function){
				Function f = (Function)op;
				Term[] subs = new Term[f.arity()];
				term.subs().toArray(subs);
				for(int i = 0; i < f.arity(); i++){
					subs[i] = replaceTermSVwithVariableSV(subs[i], s, replace);
				}
				return tb.func(f, subs);
			}
			else if(op instanceof Equality){
				Term[] subs = new Term[op.arity()];
				term.subs().toArray(subs);
				for(int i = 0; i < op.arity(); i++){
					subs[i] = replaceTermSVwithVariableSV(subs[i], s, replace);
				}
				return tb.equals(subs[0], subs[1]);
			}
			else{
				System.out.println("Bad luck the operator: " + op + " was not a function or a termSV.");
				return term;
				//TODO: implement the case that op is not a function.
			}
		}
	}

	private static Name generateName(Services s, String string) {
		StringBuilder sb = new StringBuilder(string);
		sb.append("_");
		sb.append(s.getCounter(COUNTER_NAME).getCountPlusPlus());
		return new Name(sb.toString());
	}

	private static LinkedList<AtomicRelationDescription> createAtomics(
			Iterable<Taclet> findTerms, 
			Term term, 
			ImmutableArray<Function> constructors,
			LinkedList<Pair<QuantifiableVariable, Term>> subst, 
			Services serv
	){
		LinkedList<AtomicRelationDescription> atomicRDs = new LinkedList<AtomicRelationDescription>();
		TermBuilder tb = serv.getTermBuilder();
		
		/*TODO: check whether relation descriptions have to be created for 
		have terms. Do this for all functions in the given term (t)
		*/
		
		for(Taclet findTaclet : findTerms){
			if(findTaclet instanceof FindTaclet){
				Term rangeFormula = createRangeFormula(
						term, 
						((FindTaclet) findTaclet).find(), 
						serv
				);
				if(rangeFormula != tb.ff()){	//just use rangeformula which are not false.
					atomicRDs.add(new AtomicRelationDescription(
							rangeFormula,
							constructors,
							subst,	//TODO: only use the substitutions gained from this given term (the term might be a subterm)
							serv
							));
				}
			}
		}
		
		return atomicRDs;
	}
	
	/**
	 * 
	 * @param qvs a LinkedList&lt;QuantifiableVariables&gt;
	 * @param s a Sort
	 * @return a LinkedList&lt;QuantifiableVariable&gt; which only contains QuantifiableVariables of the given Sort.
	 */
	private static LinkedList<QuantifiableVariable> getAllVariablesOfSort(LinkedList<QuantifiableVariable> qvs, Sort s){
		//TODO: [optional] check for optimization
		LinkedList<QuantifiableVariable> filtered = new LinkedList<QuantifiableVariable>();
		for(QuantifiableVariable qv : qvs){
			if(qv.sort().equals(s)){
				filtered.add(qv);
			}
		}
		return filtered;
	}
	
	/**
	 * 
	 * @param args
	 * @param offset
	 * @return a list of combinations
	 */
	private static <T> LinkedList<T[]> allCombinations(LinkedList<T>[] args, int offset){
		LinkedList<T[]> combis = new LinkedList<T[]>();
			
		if(offset < args.length){
			for(T t : args[offset]){
				for(T[] subcombi : allCombinations(args, offset + 1)){
					LinkedList<T> arrayAsList = new LinkedList<T>();
					arrayAsList.add(t);
					for(int i = 0; i < subcombi.length; i++){
						arrayAsList.add(subcombi[i]);
					}
					combis.add((T[]) arrayAsList.toArray());
				}
			}
		}
		else{
			combis.add((T[])args[offset].toArray());
		}
		
		return combis;
	}
	

	public Operator getOperator() {
		return term.op();
	}
	
	@Override
	public String toString(){
		StringBuilder sb = new StringBuilder("RelationDescription of ");
		sb.append("(");
		sb.append(term.toString());
		sb.append(")");
		return sb.toString();
	}
}
