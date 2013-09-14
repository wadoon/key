package trains.train;

public class Wagon {
	
	/*@ public invariant freeSeats >= 0; @*/
    int freeSeats;
    
    /*@ public normal_behavior
      @ requires true;
      @ ensures freeSeats>0;
      @*/
    public /*@ pure @*/ boolean hasFreeSeat(){
    	return freeSeats > 0;
    }
    
    /*@ public normal_behavior
      @ requires freeSeats >= 0;
      @ ensures \old(freeSeats) == freeSeats-1;
      @*/
    public void decreaseFreeSeats(){
    	freeSeats--;
    }
}
