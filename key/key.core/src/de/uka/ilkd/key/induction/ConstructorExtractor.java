package de.uka.ilkd.key.induction;

import java.util.LinkedList;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

public class ConstructorExtractor {

	private Term term;
	private Namespace namespace;
	
	public ConstructorExtractor(Term t, Namespace nspace) {
		this.term = t;
		this.namespace = nspace;
	}
	
	/**
	 * 
	 * @return The constructors of term as ImmutableArray&lt;Function&gt; 
	 */
	public ImmutableArray<Function> getConstructors(){
		LinkedList<Function> constructors = new LinkedList<Function>();
		SortExtractor extractor = new SortExtractor();
		ImmutableArray<Sort> sortsOfTerm;
		ImmutableList<Named> functions = namespace.allElements();
		
		//extract the sorts of term
		extractor.addTermWithAllSubterms(this.term);
		sortsOfTerm = extractor.getSorts();
		
		
		
		return new ImmutableArray<Function>(constructors);
	}
	
	/**
	 * 
	 * @param f a function
	 * @return true if the function is a constructor else false. 
	 */
	private boolean isConstructor(Function f){
		//TODO: do some better heuristic on the problem whether a function is a constructor or not.
		return f.isUnique();
	}

}
