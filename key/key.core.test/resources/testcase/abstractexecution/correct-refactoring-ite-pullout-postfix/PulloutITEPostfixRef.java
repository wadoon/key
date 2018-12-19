public class PulloutITEPostfixRef {
    public int before(int result, boolean b) {
        if (b) {
            abstract_program Q1;
            abstract_program P;
        } else {
            abstract_program Q2;
            abstract_program P;
        }
        
        return result;
    }
    
    public int after(int result, boolean b) {
        if (b) {
            abstract_program Q1;
        } else {
            abstract_program Q2;
        }
        abstract_program P;
        
        return result;
    }
}