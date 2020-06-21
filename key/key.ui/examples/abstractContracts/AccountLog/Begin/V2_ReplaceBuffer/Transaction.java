public class Transaction {
	/*@ accessible \inv:this.*; @*/
	
	Log log = new Log(10);
	
	/*@ public normal_behavior
	  requires_abs transferR1;
	  requires_abs transferR2;
	  def transferR1 = destination != null && source != null && \invariant_for(source) 
	  		&& \invariant_for(destination) && \invariant_for(log);
	  def transferR2 = source != destination;
	  ensures_abs transferE1;
	  ensures_abs transferE2;
	  ensures_abs transferE3;
	  def transferE1 = \result ==> (\old(destination.balance) + amount == destination.balance);
	  def transferE2 = \result ==> (\old(source.balance) - amount == source.balance);
	  def transferE3 = log.last == (\old(log.last) == \old(log.logRecord.length)  - 1 ? 0 : \old(log.last) + 1) && 
               log.logRecord[log.last] == refNum;
	  assignable_abs transferA;
	  def transferA = log.logRecord, log.logRecord[log.last + 1], log.last, source.balance, destination.balance;
	 @*/
	public boolean transfer(Account source, Account destination, int amount, int refNum) {
		
		log.add(refNum);
		
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