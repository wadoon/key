public class Account {
	final int OVERDRAFT_LIMIT = 0;
	
	/*@ accessible \inv:this.*; @*/
	
	//@ public invariant balance >= OVERDRAFT_LIMIT;
	
	int balance = 0;
	public boolean lock = false;
	
	/*@
	 @ ensures balance == 0;
	 @*/
	Account() {
	}
	
	/*@ 
	 @ public normal_behavior
	 @ ensures (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) + x); 
	 @ assignable balance;
	 @*/
	boolean update(int x) {
		int newBalance = balance + x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}

	/*@ 
	 @ public normal_behavior
	 @ ensures (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) - x);
	 @ assignable balance;
	 @*/
	boolean undoUpdate(int x) {
		int newBalance = balance - x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}
	
	/*@
	 @ public normal_behavior
	 @ ensures this.lock;
	 @ assignable this.lock;
	 @*/
	void lock() {
		lock = true;
	}
	
	/*@
	 @ public normal_behavior
	 @ ensures !this.lock;
	 @ assignable this.lock;
	 @*/
	void unLock() {
		lock = false;
	}
	
	/*@
	 @ public normal_behavior
	 @ ensures \result == this.lock;
	 @*/
	boolean /*@ pure @*/ isLocked() {
		return lock;
	}
	
}