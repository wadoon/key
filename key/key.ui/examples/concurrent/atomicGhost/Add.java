final class Add {

	int x;
	//@ atomic ghost boolean c;
	
	/*@ requires !c;
	  @ ensures c;
	  @ ensures c ==> x == \old(x)+y;
	  @*/
	void add (int y) {
		x+= y;
		//@ set c = true;
	}
}
