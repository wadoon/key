public class Account {

	/*@ accessible \inv:this.*; @*/
	
	int balance = 0;
	public boolean lock = false;
	
	/*@
	 @ ensures balance == 0;
	 @*/
	Account() {
	}
	
	/*@
	 @ public normal_behavior
	 @ ensures (balance == \old(balance) + x) && \result; 
	 @ assignable balance;
	 @*/
	boolean update(int x) {
		balance = balance + x;
		return true;
	}

	/*@ 
	 @ public normal_behavior
	 @ ensures (balance == \old(balance) - x) && \result;
	 @ assignable balance;
	 @*/
	boolean undoUpdate(int x) {
		balance = balance - x;
		return true;
	}
	
	/*@
	 @ public normal_behavior
	 @ ensures \result == this.lock;
	 @*/
	boolean /*@ pure @*/ isLocked() {
		return lock;
	}
	
}