package de.uka.ilkd.key.specgen.verificationrelationsystem.verificationrelation;

public class VerificationRelation {

	private Placeholder mySourcePlaceholder;
	private Phi myCondition;
	private Delta myChange;
	private Placeholder myDestinationPlaceholder;
	
	public VerificationRelation(Placeholder sourcePlaceholder, Phi condition, Delta change, Placeholder destinationPlaceholder) {
		mySourcePlaceholder = sourcePlaceholder;
		myCondition = condition;
		myChange = change;
		myDestinationPlaceholder = destinationPlaceholder;
	}
	
	public Placeholder getSourcePlaceholder() {
		return mySourcePlaceholder;
	}
	public Phi getCondition() {
		return myCondition;
	}
	public Delta getChange() {
		return myChange;
	}
	public Placeholder getDestinationPlaceholder() {
		return myDestinationPlaceholder;
	}
	
	@Override
	public String toString() {
		String result = "";
		result = result + mySourcePlaceholder + "," + myCondition
						+ " ⊨ "
						+ myChange + myDestinationPlaceholder;
		return result;
	}
	
}
