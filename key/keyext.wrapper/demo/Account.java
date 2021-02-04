class Account {

	final static int OVERDRAFT_LIMIT = 0;

	int balance = 0;
	
	/*@
	 @ ensures (!\result ==> balance == \old(balance)) 
	 @   && (\result ==> balance == \old(balance) + x); 
	 @*/
	boolean update(int x) {
		int newBalance = balance + x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}

}
