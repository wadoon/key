public class Account {
	final int OVERDRAFT_LIMIT = 0;
	final int FEE = 1;
	
	/*@ accessible \inv:this.*; @*/
	
	//@ public invariant balance >= OVERDRAFT_LIMIT;
	//@ public invariant FEE >= 0;
	
	int balance = 0;
	public boolean lock = false;
	
	/*@
	 @ ensures balance == 0;
	 @*/
	Account() {
	}
	
	/*@ 
	 @ public normal_behavior
	 @ requires_abs updateR;
	 @ def updateR = true;
	 @ ensures_abs updateE;
	 @ def updateE =  (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) + x - FEE); 
	 @ assignable balance;
	 @*/
	boolean update(int x) {
		int newBalance = balance + x - FEE;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}

	/*@ 
	 @ public normal_behavior
	 @ requires_abs undoUpdateR;
	 @ def undoUpdateR = true;
	 @ ensures_abs undoUpdateE;
	 @ def undoUpdateE =  (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) - x - FEE);
	 @ assignable balance;
	 @*/
	boolean undoUpdate(int x) {
		int newBalance = balance - x - FEE;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}
	
	/*@
	 @ ensures_abs lockE;
	 @ def lockE = this.lock;
	 @ assignable_abs lockA;
	 @ def lockA = this.lock;
	 @*/
	void lock() {
		lock = true;
	}
	
	/*@
	 @ ensures_abs unLockE;
	 @ def unLockE = !this.lock;
	 @ assignable_abs unLockA;
	 @ def unLockA = this.lock;
	 @*/
	void unLock() {
		lock = false;
	}
	
	/*@
	 @ public normal_behavior
	 @ ensures_abs isLockedE;
	 @ def isLockedE = \result == this.lock;
	 @*/
	boolean /*@ pure @*/ isLocked() {
		return lock;
	}
}