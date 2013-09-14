package train;

public class Train {
//@ public instance ghost non_null Wagon[] _wagons ;
	
	ArrayList /*@ non_null @*/ wagons;

	public static Train createLocomotive(){
		return new Train();
	}

	Train(){
		wagons = new ArrayList();
	}

	public boolean /*@ pure @*/ hasWagon(Wagon w){
		return wagons.contains(w);
	}


/*@
  public normal_behavior
  ensures hasWagon(w);
  assignable _wagons;
 @*/
	public void addWagon(Wagon w){
		wagons.add(w);
	}
}

