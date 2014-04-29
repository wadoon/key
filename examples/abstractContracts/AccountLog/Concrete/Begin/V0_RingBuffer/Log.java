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
      @ requires true;
      @ ensures (\result == (last == logRecord.length - 1 ? 0 : last + 1));
      @ assignable \nothing;
      @*/
    protected /*@ pure @*/ int rotateLog() {
	return (last + 1) % logRecord.length;
    }

    /*@ public normal_behavior
      @ requires   true;
      @ ensures    (last == (\old(last) == logRecord.length - 1 ? 0 : \old(last) + 1)) && 
      @             (logRecord[last] == bal);
      @ assignable logRecord[(last + 1) % logRecord.length], last;
      @*/
    public void add(int bal) {
	last = rotateLog();
        logRecord[last] = bal;
    }


}
