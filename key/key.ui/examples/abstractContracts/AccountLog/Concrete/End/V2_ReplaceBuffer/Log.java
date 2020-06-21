public class Log {
	
	/*@ accessible \inv:this.*; @*/
	
    //@ public invariant logRecord.length > 0;
    protected int[] logRecord;

    //@ public invariant last >=-1 && last < logRecord.length;
    protected int last;
   
    public Log(int size) {
	this.logRecord = new int[size];
	last = -1;
    }
   
    /*@ public normal_behavior
      @ requires true;
      @ ensures  (\result == ((logRecord.length - 1 == \old(last)) ? 0 : \old(last) + 1)) &&
      @      ((logRecord.length - 1 == \old(last)) ==> 
      @             ( \fresh(logRecord) &&
      @               (\forall int i; i>=0 && i<logRecord.length; logRecord[i] == 0) &&
      @               logRecord.length == \old(logRecord.length))) &&
      @      ((logRecord.length - 1 > \old(last)) ==> logRecord == \old(logRecord));
      @ assignable logRecord;
      @*/
    public int rotateLog() {
	if (last == logRecord.length - 1) {
	    logRecord = new int[logRecord.length];
	    return 0;
	} else {
	    return last + 1;
	}
    }

    /*@ public normal_behavior
      @ requires   true;
      @ ensures    last == (\old(last) == \old(logRecord.length) - 1 ? 0 : \old(last) + 1) && 
      @                logRecord[last] == bal;
      @ assignable logRecord, last, logRecord[last + 1];
      @*/
    public void add(int bal) {
	last = rotateLog();
        logRecord[last] = bal;
    }


}
