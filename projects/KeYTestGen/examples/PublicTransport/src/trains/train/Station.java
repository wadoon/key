package trains.train;

public class Station {

    //public static final Station CENTRAL = new Station("CENTRAL");
    
    private String name;
	
	public Station(String str){
		name = str;
	}
	
	/*@ public normal_behavior
	  @ requires t != null && w != null;
	  @ ensures t.hasWagon(w);
	  @*/
	public void addWagon(Train t, Wagon w){
		t.addWagon(w);			
	}
}