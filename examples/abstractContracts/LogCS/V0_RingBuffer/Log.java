public class Log {


    //@ public invariant logRecord.length > 0;
    private int[] logRecord;

    //@ public invariant last >= -1 && last < logRecord.length;
    private int last;
   
    public Log(int size) {
	this.logRecord = new int[size];
	last = -1;
    }
   
    /*@ public normal_behavior
      @ requires_abs rotateLogR;
      @ ensures_abs rotateLogE;
      @ assignable_abs rotateLogA;
      @ def rotateLogR = true;
      @ def rotateLogE = (\result == (last == logRecord.length - 1 ? 0 : last + 1));
      @ def rotateLogA = \nothing;
      @*/
    protected /*@ pure @*/ int rotateLog() {
	return (last + 1) % logRecord.length;
    }

    /*@ public normal_behavior
      @ requires_abs   Log_addR;
      @ ensures_abs    Log_addE;
      @ assignable_abs Log_addA;
      @ def Log_addR = true;
      @ def Log_addE = (last == (\old(last) == logRecord.length - 1 ? 0 : \old(last) + 1)) && 
      @             (logRecord[last] == bal);
      @ def Log_addA = logRecord[(last + 1) % logRecord.length], last;
      @*/
    public void add(int bal) {
	last = rotateLog();
        logRecord[last] = bal;
    }


}
