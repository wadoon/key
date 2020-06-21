public class Log {
	/*@ accessible \inv:this.*; @*/

    //@ public invariant logRecord.length > 0;
    protected int[] logRecord;

    //@ public invariant last >= -1 && last < logRecord.length;
    protected int last;
   
    public Log(int size) {
	this.logRecord = new int[size];
	last = -1;
    }
   
    /*@ public normal_behavior
      @ requires_abs rotateLogR;
      @ ensures_abs rotateLogE;
      @ assignable_abs rotateLogA;
      @ def rotateLogR = true;
      @ def rotateLogE = (\result == ((logRecord.length-1 == last) ? 0 : last + 1)) &&
      @     ((logRecord.length-1 == last) ==>  (\forall int i; i>=0 && i<logRecord.length; logRecord[i] == 0));
      @ def rotateLogA = logRecord[*];
      @*/
    public int rotateLog() {
	if (last == logRecord.length - 1) {
	    // empty array
	    /*@ loop_invariant
	      @   i>=0 && i<=logRecord.length &&
	      @   (\forall int j; j>=0 && j<i; logRecord[j] == 0);
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
      @ requires_abs   Log_addR;
      @ ensures_abs    Log_addE;
      @ assignable_abs Log_addA;
      @ def Log_addR = true;
      @ def Log_addE = last == (\old(last) == logRecord.length  - 1 ? 0 : \old(last) + 1) && 
      @                logRecord[last] == bal;
      @ def Log_addA = logRecord[*], last;
      @*/
    public void add(int bal) {
	last = rotateLog();
        logRecord[last] = bal;
    }


}
