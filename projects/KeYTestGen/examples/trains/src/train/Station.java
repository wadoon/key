package train;

public class Station {
	/*@
	 public normal_behavior
	 requires t != null && w != null;
	 ensures t.hasWagon(w);
	 @*/
	public void addWagon(Train t, Wagon w){
		t.addWagon(w);
	}
}
