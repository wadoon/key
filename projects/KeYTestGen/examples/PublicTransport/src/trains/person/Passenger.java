package trains.person;

import trains.train.*;

public class Passenger {
	
	/*@ public invariant currentTrain == null <==> currentWagon == null; @*/
	/*@ public invariant currentTrain == null <==> currentStation != null; @*/
	public Train currentTrain = null;
	public Station currentStation = null;
	public Wagon currentWagon = null;
	
	/*@ public normal_behavior
	  @ requires t != null;
	  @ ensures \old(currentStation) == t.getNextStation() &&
	  @       ((\exists int i ; 0<=i && i< t.length(); t.getWagon(i) == currentWagon) 
	  @         ==> currentTrain == t && currentStation == null); 
	  @*/
	public boolean takeTrain(Train t){
		if(currentTrain == null && this.currentStation == t.getNextStation()) {
			currentTrain = t;
			
			for(int i = 0; i<t.length(); i++){
				Wagon cv = t.getWagon(i);
				if(cv.hasFreeSeat()){
					currentWagon = cv;
					currentStation = null;
					cv.decreaseFreeSeats();
					return true;
				}
			}		
		}
		/*
		  @ \assignable currentTrain;
		  @ \assignable currentStation; 
		  @ \assignable currentWagon;
		  
		  && st != null
		  */
		return false;
	}
	
	/*@ public normal_behavior
	  @ ensures \old(currentTrain) == null ==> !\result;
	  @ ensures \old(currentTrain) != null ==> \result &&
	  @										currentTrain == null &&
	  @           							currentWagon == null &&
	  @           							currentStation == \old(currentTrain).getNextStation();
	  @*/
	public boolean getOffTrain(){
		if(currentTrain == null && currentWagon == null){
			return false;
		}
		else{
			currentStation = currentTrain.getNextStation();
			currentTrain = null;
			currentWagon = null;	
			return true;
		}			
	}
}