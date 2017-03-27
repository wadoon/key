package de.uka.ilkd.key.induction;

import java.util.LinkedList;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

public class ConstructorExtractor {

	private Term term;
	private Namespace namespace;
	private ImmutableArray<Sort> sortsOfTerm;
	
	public ConstructorExtractor(Term t, Services s) {
		this.term = t;
		this.namespace = s.getNamespaces().functions();
		
		//extract sorts from term
		SortExtractor extractor = new SortExtractor();
		extractor.addTermWithAllSubterms(this.term);
		sortsOfTerm = extractor.getSorts();
	}
	
	/**
	 * 
	 * @return The constructors of term as ImmutableArray&lt;Function&gt; 
	 */
	public ImmutableArray<Function> getConstructors(){
		LinkedList<Function> constructors = new LinkedList<Function>();
		ImmutableList<Named> functions = namespace.allElements();
		
		for(Named n: functions){
			if(n instanceof Function){
				Function f = (Function) n;
				//check whether the function is a constructor of a sort in the term
				if(isConstructor(f)){
					constructors.add(f);
				}
			}
		}
		
		return new ImmutableArray<Function>(constructors);
	}
	
	/**
	 * 
	 * @param f a function
	 * @return true if the function is a constructor else false. 
	 */
	private boolean isConstructor(Function f){
		//TODO: do some better heuristic on the problem whether a function is a constructor or not.
		return f.isUnique() && sortsOfTerm.contains(f.sort());
	}

}
