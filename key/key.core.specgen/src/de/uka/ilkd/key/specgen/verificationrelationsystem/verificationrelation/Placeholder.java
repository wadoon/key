package de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation;

import java.util.List;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.specgen.utility.UniqueCounter;

public class Placeholder {

	private final String myName;
	private final Term[] myTerms;
	private final Sort[] mySorts;
	private final LocationVariable[] myVariables;
	private final Function myFunction;
	private final Term myInstance;
		
	public Placeholder(String name, List<LocationVariable> variables, TermBuilder termBuilder) {
		myTerms = new Term[variables.size()];
		mySorts = new Sort[variables.size()];
		myVariables = new LocationVariable[variables.size()];
		for(int i=0; i<variables.size(); i++) {
			LocationVariable currentVariable = variables.get(i);
			myTerms[i] = termBuilder.var(currentVariable);
			mySorts[i] = currentVariable.sort();
			myVariables[i] = currentVariable;
		}
		UniqueCounter uniqueCounter = UniqueCounter.getInstance();
		int id = uniqueCounter.getNext();
		myName = name + "_" + id;
		myFunction = new Function( new Name(myName), Sort.FORMULA, mySorts );
		myInstance = termBuilder.func( myFunction, myTerms );
	}
	
	public String getName() {
		return myName;
	}
	public LocationVariable[] getVariables() {
		return myVariables;
	}
	
	public Term getInstance() {
		return myInstance;
	}
	
	@Override
	public String toString() {
		String result = "";
		result = result + myName;
		if(myVariables != null) {
			result = result + "[";
			boolean first = true;
			for(LocationVariable currentVariable : myVariables) {
				if(!first) result = result + ",";
				result = result + currentVariable;
				first = false;
			}
			result = result + "]";
		}
		return result;
	}
	
}
