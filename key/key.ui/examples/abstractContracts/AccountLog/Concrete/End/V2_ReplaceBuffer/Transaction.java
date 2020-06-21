public class Transaction {
	/*@ accessible \inv:this.*; @*/
	
	Log log = new Log(10);
	
	/*@ public normal_behavior
	  requires destination != null && source != null && \invariant_for(source) 
	  		&& \invariant_for(destination) && \invariant_for(log);
	  requires source != destination;
	  ensures \result ==> (\old(destination.balance) + amount == destination.balance);
	  ensures \result ==> (\old(source.balance) - amount == source.balance);
	  ensures \result ==> log.last == (\old(log.last) == \old(log.logRecord.length)  - 1 ? 0 : \old(log.last) + 1) && 
               log.logRecord[log.last] == bal;
	  assignable log.logRecord, log.logRecord[log.last + 1], log.last, source.balance, destination.balance;
	 @*/
	public boolean transfer(Account source, Account destination, int amount, int bal) {
		
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
		log.add(bal);
		return true;	
		
	}
}