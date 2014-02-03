public class Simple {
    public int l;
    private int h;
    /*@ public normal_behavior 
     @ ensures \result >=l;
     @*/
	public int magic() {
            if(h>0)
                return l;
            else return l+10;
	}
}