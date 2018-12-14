public class PulloutITEPostfixRef {
    public int before(int result, boolean b) {
        if (b) {
            abstract-program Q1;
            abstract-program P;
        } else {
            abstract-program Q2;
            abstract-program P;
        }
        
        return result;
    }
    
    public int after(int result, boolean b) {
        if (b) {
            abstract-program Q1;
        } else {
            abstract-program Q2;
        }
        abstract-program P;
        
        return result;
    }
}