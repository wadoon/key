public class Account {
	final int OVERDRAFT_LIMIT = 0;
	final static int DAILY_LIMIT = -1000;
	
	/*@ accessible \inv:this.*; @*/
	
	//@ public invariant balance >= OVERDRAFT_LIMIT;
	int balance = 0;
	
	//@ invariant withdraw >= DAILY_LIMIT;
	int withdraw = 0;
	
	public boolean lock = false;
	
	/*@
	 @ ensures balance == 0;
	 @*/
	Account() {
	}
	
	/*@ public normal_behavior
	 @ requires_abs updateR;
	 @ def updateR = true;
	 @ ensures_abs updateE;
	 @ def updateE = (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) + x)
	 @	 && (!\result ==> withdraw == \old(withdraw)) 
	 @   && (\result ==> withdraw <= \old(withdraw));
	 @ assignable_abs updateA;
	 @ def updateA = balance;
	 @*/
	boolean update(int x) {
		int newWithdraw = withdraw;
		if (x < 0)  {
			newWithdraw += x;
			if (newWithdraw < DAILY_LIMIT) 
				return false;
		}
		int newBalance = balance + x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		withdraw = newWithdraw;
		return true;
	}

	/*@ public normal_behavior
	 @  requires_abs undoUpdateR;
	 @  def undoUpdateR = true;
	 @ ensures_abs undoUpdateE;
	 @ def undoUpdateE = (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) - x)
	 @   && (!\result ==> withdraw == \old(withdraw)) 
	 @   && (\result ==> withdraw >= \old(withdraw));
	 @ assignable_abs undoUpdateA;
	 @ def undoUpdateA = balance;
	 @*/
	boolean undoUpdate(int x) {
		int newWithdraw = withdraw;
		if (x < 0)  {
			newWithdraw -= x;
			if (newWithdraw < DAILY_LIMIT) 
				return false;
		}
		int newBalance = balance - x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		withdraw = newWithdraw;	
	
		return true;
	}
	
	/*@
	 @ ensures this.lock;
	 @ assignable lock;
	 @*/
	void lock() {
		lock = true;
	}
	
	/*@
	 @ ensures !this.lock;
	 @ assignable lock;
	 @*/
	void unLock() {
		lock = false;
	}
	
	/*@
	 @ ensures \result == this.lock;
	 @*/
	boolean /*@ pure @*/ isLocked() {
		return lock;
	}
	
}
