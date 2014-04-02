public class Transaction {
	/*@ accessible \inv:this.*; @*/

	/*@ public normal_behavior
	  requires_abs transferR1;
	  requires_abs transferR2;
	  def transferR1 = destination != null && source != null && \invariant_for(source) 
	  		&& \invariant_for(destination);
	  def transferR2 = source != destination;
	  ensures_abs transferE1;
	  ensures_abs transferE2;
	  def transferE1 = \result ==> (\old(destination.balance) + amount >= destination.balance);
	  def transferE2 = \result ==> (\old(source.balance) - amount >= source.balance);
	 @*/
	public boolean transfer(Account source, Account destination, int amount) {
		if (amount <= 0) {
			return false;
		}
		if (!source.update(amount * -1)) {
			return false;
		}
		if (!destination.update(amount)) {
			source.undoUpdate(amount * -1);
			return false;
		}
		return true;
	}

	/*@
	  requires destination != null && source != null && \invariant_for(source) 
	  		&& \invariant_for(destination);
	  requires source != destination;
	  ensures \result ==> source.lock && destination.lock;
	  assignable source.lock, destination.lock;
	 @*/
	public static synchronized boolean lock(Account source, Account destination) {
		if (source.isLocked()) return false;
		if (destination.isLocked()) return false;
		source.lock();
		destination.lock();
		return true;
	}
}