public class PulloutITEPrefixRef {
    public int before(int result, boolean b) {
        if (b) {
            abstract-program P;
            abstract-program Q1;
        } else {
            abstract-program P;
            abstract-program Q2;
        }
        
        return result;
    }
    
    public int after(int result, boolean b) {
        //@ assignable_not b, result;
        { abstract-program P; }
        if (b) {
            abstract-program Q1;
        } else {
            abstract-program Q2;
        }
        
        return result;
    }
}