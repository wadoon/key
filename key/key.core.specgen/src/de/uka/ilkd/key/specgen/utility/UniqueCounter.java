package de.uka.ilkd.key.specgen.utility;

public class UniqueCounter {

	private int myCounter;
	
	private static UniqueCounter INSTANCE;
	
	public static UniqueCounter getInstance() {
		if(INSTANCE == null) {
			INSTANCE = new UniqueCounter();
		}
		return INSTANCE;
	}
	private UniqueCounter() {
		myCounter = 0;
	}
	
	public int getNext() {
		int currentCounter = myCounter;
		myCounter = myCounter + 1;
		return currentCounter;
	}	
	
	@Override
	public String toString() {
		String result = "";
		result = result + myCounter;
		return result;
	}
	
}
