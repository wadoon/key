public class Account {

	/*@ accessible \inv:this.*; @*/
	
	int balance = 0;
	
	/*@
	 @ ensures balance == 0;
	 @*/
	Account() {
	}
	
	/*@ public normal_behavior
	 @ ensures (balance == \old(balance) + x) && \result; 
	 @ assignable balance;
	 @*/
	boolean update(int x) {
		balance = balance + x;
		return true;
	}

	/*@ public normal_behavior
	 @  ensures (balance == \old(balance) - x) && \result;
	 @  assignable balance;
	 @*/
	boolean undoUpdate(int x) {
		balance = balance - x;
		return true;
	}

	
}