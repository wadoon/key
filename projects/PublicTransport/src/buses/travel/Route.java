package buses.travel;

public class Route {
  
	String start;
	String end;
	
	public String getStart() {
		return start;
	}
	public String getEnd() {
		return end;
	}
	
  public Route(String start, String end){
	  this.start = start;
	  this.end = end;
  }
}
