public class Log {

	/*@ accessible \inv:this.*; @*/
		
    //@ public invariant logRecord.length > 0;
    int[] logRecord;

    //@ public invariant last >=-1 && last < logRecord.length;
    int last;
	
	public Log(int size) {
		this.logRecord = new int[size];
		last = -1;
    }
   
    /*@ public normal_behavior
      @ requires true;
      @ ensures  (\result == ((logRecord.length-1 == last) ? 0 : last + 1)) &&
      @     ((logRecord.length-1 == last) ==>  (\forall int i; i>=0 && i<logRecord.length; logRecord[i] == 0));
      @ assignable logRecord[*];
      @*/
      public int rotateLog() {
    	if (last == logRecord.length - 1) {
	    // empty array
	    /*@ loop_invariant
	      @   i>=0 && i<=logRecord.length &&
	      @   	(\forall int j; j>=0 && j<i; logRecord[j] == 0);
	      @ decreases logRecord.length - i;
	      @ assignable logRecord[*];
	      @*/
				for (int i = 0; i<logRecord.length; i++) {
					logRecord[i] = 0;		
	   		}
	    	return 0;
			} else {
	   		return last + 1;
				}
			}

    /*@ public normal_behavior
      @ requires true;
      @ ensures last == (\old(last) == logRecord.length  - 1 ? 0 : \old(last) + 1) && 
      @         logRecord[last] == bal;
      @ assignable logRecord[*], last;
      @*/
    public void add(int bal) {
	last = rotateLog();
        logRecord[last] = bal;
    }


}
