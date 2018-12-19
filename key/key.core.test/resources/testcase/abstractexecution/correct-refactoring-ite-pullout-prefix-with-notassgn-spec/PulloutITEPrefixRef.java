public class PulloutITEPrefixRef {
    public int before(int result, boolean b) {
        if (b) {
            abstract_program P;
            abstract_program Q1;
        } else {
            abstract_program P;
            abstract_program Q2;
        }
        
        return result;
    }
    
    public int after(int result, boolean b) {
        //@ assignable_not b;
        { abstract_program P; }
        if (b) {
            abstract_program Q1;
        } else {
            abstract_program Q2;
        }
        
        return result;
    }
}