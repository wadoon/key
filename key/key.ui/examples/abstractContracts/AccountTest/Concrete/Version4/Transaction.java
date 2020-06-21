public class Transaction {
	/*@ accessible \inv:this.*; @*/

	/*@ public normal_behavior
	  requires destination != null && source != null && \invariant_for(source) 
	  		&& \invariant_for(destination);
	  requires source != destination;
	  ensures true;
	  ensures (amount <= 0) ==> !\result;
	  assignable \everything;
	 @*/
	public boolean transfer(Account source, Account destination, int amount) {
		if (source.balance < 0) amount = -1;
		if (destination.isLocked()) amount = -1;
		if (source.isLocked()) amount = -1;
		
		int take;
		int give;
		if (amount != -1) { take = amount * -1; give = amount;} 
	
		if (amount <= 0) {
			return false;
		}
		if (!source.update(take)) {
			return false;
		}
		if (!destination.update(give)) {
			source.undoUpdate(take);
			return false;
		}
		return true;	
	}
}