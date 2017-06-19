package de.uka.ilkd.key.induction;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.util.Pair;

public class AtomicRelationDescription {
	
	/** a quantifier-free formula 
	 * needed: 
	 *  - access to all variables of the formula
	 *  - the formula need to be a boolean
	 * */
	private Term rangeFormula;	//make sure that term is the right class to handle the range formula
	
	/** TODO: find fitting description. 
	 * this should not be empty */
	private LinkedList<Pair<QuantifiableVariable, Term>> domainSubstitution;
	private Taclet findTaclet;
	private Term original;
	private Services services;
	private RelationDescription parent;
	private LinkedList<QuantifiableVariable> vars;
	
	public AtomicRelationDescription(
			Term range, 
			ImmutableArray<Function> constructors, 
			Term originalTerm, 
			FindTaclet taclet,
			RelationDescription parent,
			Services serv
	){
		vars = new LinkedList<>();
		rangeFormula = range;		
		original = originalTerm;
		domainSubstitution = new LinkedList<>();
		findTaclet = taclet;
		services = serv;
		this.parent = parent;
		collectVars(range.sub (1));
	}
	
	/**
	 * This function collects all QuantifiableVariables from a Term and adds them to the private 
	 * variable vars.
	 * 
	 * @param t a formula
	 */
	private void collectVars(Term t){
		if(t.op() instanceof QuantifiableVariable){
			vars.add((QuantifiableVariable) t.op());
		}
		else{
			for(Term sub : t.subs()){
				collectVars(sub);
			}
		}
	}
	
	/**
	 * 
	 * @return Set&lt;Variable&gt;: all variables used in rangeFormula and/or domainSubstitution.
	 */
	public LinkedList<QuantifiableVariable> getRelevantVariables(){
		LinkedList<QuantifiableVariable> relevantVars = null;	//Find the most useful type of set
		
		addTermVars(relevantVars, rangeFormula);
		
		for(Pair<QuantifiableVariable, Term> subst : this.domainSubstitution){
			addIfNotContains(relevantVars, subst.first);
			addTermVars(relevantVars, subst.second);
		}
		
		return relevantVars;
	}
	
	/**
	 * 
	 * @return a List of Pairs of QuantifiableVariable and Term which is the domainSubstitution
	 */
	public List<Pair<QuantifiableVariable, Term>> getSubstitutions(){
		
		return this.domainSubstitution;
	}
	
	/**
	 * 
	 * @param list a LinkedList of any type
	 * @param element an element of the same type as the given list. This element is added to the
	 * list if this list does not contain it already.
	 */
	private <T> void addIfNotContains(LinkedList<T> list, T element){
		if(!list.contains(element)){
			list.add(element);
		}
	}
	
	/**
	 * 
	 * @param list a list of QuantifiableVariables
	 * @param t the term whose variables should be added to the given list.
	 */
	private void addTermVars(LinkedList<QuantifiableVariable> list, Term t){
		ImmutableSet<QuantifiableVariable> freeVarsOfRangeFormula = t.freeVars();	//transform into variables
		ImmutableArray<QuantifiableVariable> boundVarsOfRangeFormula = t.boundVars();	//transform into variables
		
		for(QuantifiableVariable qv : freeVarsOfRangeFormula){
			addIfNotContains(list, qv);
		}
		
		for(QuantifiableVariable qv : boundVarsOfRangeFormula){
			addIfNotContains(list, qv);
		}
	}
	
	/**
	 * @return a LinkedList of QuantifiableVariables.
	 */
	public LinkedList<QuantifiableVariable> getInductionVariables(){
		return vars;
	}
	
	/**
	 * @return the range-formula of this AtomicRelationDescription as Term.
	 */
	public Term getRange(){
		return this.rangeFormula;
	}
	
	/**
	 * 
	 * @return the Term which represents the induction hypothesis needed to proof case of this 
	 * atomic relation-description.
	 */
	public Term getHypothesis(){
		ImmutableList<TacletGoalTemplate> goals = findTaclet.goalTemplates();
		TermBuilder tb = services.getTermBuilder();
		Term replaceTerm = null;
		for(TacletGoalTemplate goal : goals){
			Object obj = goal.replaceWithExpressionAsObject();
			if(obj instanceof Term){
				replaceTerm = (Term)obj;
			}
		}
		
		if(replaceTerm != null){
			Term buildTerm = parent.getBuildTerm();
			Term hypothesis = tb.tt();
			
			LinkedHashSet<Pair<QuantifiableVariable, Term>> subst = new LinkedHashSet<>();
			
			for(Term t : getOccurences((Function) buildTerm.op(), replaceTerm)){
				subst.addAll(getSubstPart(t, buildTerm));
			}
			
			this.domainSubstitution.addAll(subst);
			
			for(Pair<QuantifiableVariable, Term> pair : subst){
				hypothesis = tb.and(hypothesis, tb.subst(pair.first, pair.second, original.sub(0)));
			}
			
			
			return hypothesis;
		}else{
			return tb.tt();
		}
	}
	
	/**
	 * Warning: this function does not check for equality with respect to functions!
	 * @param newTerm a substituted Term
	 * @param oldTerm the "older" version of newTerm (without) substitutions.
	 * @return a LinkedList of Pairs of QuantifiableVariable and Term which contains substitutions 
	 * which can replace the QuantifiableVariables from oldTerm with the Term which are at the 
	 * same position at newTerm. This means this function reconstructs the substitutions which are 
	 * need to build newTerm from oldTerm.
	 */
	private LinkedHashSet<Pair<QuantifiableVariable, Term>> getSubstPart(Term newTerm, Term oldTerm){
		LinkedHashSet<Pair<QuantifiableVariable, Term>> result = new LinkedHashSet<>();
		
		if(oldTerm.op() instanceof QuantifiableVariable){
			for(Term t : getTermOfSort(newTerm)){
				result.add(new Pair<QuantifiableVariable, Term>((QuantifiableVariable) oldTerm.op(), t));
			}
		}
		else{
			for(int i = 0; i < oldTerm.arity(); i++){
				result.addAll(getSubstPart(newTerm.sub(i), oldTerm.sub(i)));
			}
		}
		return result;
	}
	
	/**
	 * 
	 * @param t a Term.
	 * @return a Term which only consists of a QuantifiableVariable. It is the first variable of 
	 * the variable vars which has the same type as the given term.
	 */
	private LinkedHashSet<Term> getTermOfSort(Term t){
		LinkedHashSet<Term> selection = new LinkedHashSet<>();
		for(QuantifiableVariable qv : vars){
			if(qv.sort() == t.sort()){
				selection.add(this.services.getTermBuilder().var(qv));
			}
		}
		return selection;
	}
	
	/**
	 * 
	 * @param f a Function
	 * @param t a Term
	 * @return a LinkedList of Terms which contains all occurences of the given Function f in the 
	 * given Term t.
	 */
	private LinkedList<Term> getOccurences(Function f, Term t){
		LinkedList<Term> terms = new LinkedList<>();
		if(t.op() == f){
			terms.add(t);
		}
		else{
			for(Term sub : t.subs()){
				terms.addAll(getOccurences(f, sub));
			}
		}
		return terms;
	}
	
	/**
	 * 
	 */
	@Override
	public String toString(){
		StringBuilder sb = new StringBuilder();
		boolean firstElement = true;
		sb.append("Range Formula:");
		sb.append(this.rangeFormula.toString());
		sb.append(", Substitutions: ");
		if(this.domainSubstitution != null){
			for(Pair<QuantifiableVariable, Term> subst : this.domainSubstitution){
				if(!firstElement){
					sb.append(", ");
				}
				else{
					firstElement = false;
				}
				sb.append("{");
				sb.append(subst.first.toString());
				sb.append("\\");
				sb.append(subst.second.toString());
				sb.append("}");
			}
		}
		else{
			sb.append("no substitution found.");
		}
		return sb.toString();
	}
}
