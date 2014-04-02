public class Account {

	/*@ accessible \inv:this.*; @*/
	
	int balance = 0;
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
	 @ def updateE = (balance == \old(balance) + x) && \result; 
	 @ assignable balance;
	 @*/
	boolean update(int x) {
		balance = balance + x;
		return true;
	}

	/*@ public normal_behavior
	 @  requires_abs undoUpdateR;
	 @  def undoUpdateR = true;
	 @  ensures_abs undoUpdateE;
	 @  def undoUpdateE = (balance == \old(balance) - x) && \result;
	 @  assignable balance;
	 @*/
	boolean undoUpdate(int x) {
		balance = balance - x;
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
	 @ ensures \result == this.lock;
	 @*/
	boolean /*@ pure @*/ isLocked() {
		return lock;
	}
	
}