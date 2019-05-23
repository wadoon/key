public class BasicArrayTests {
    /*@ public normal_behavior
      @ requires A != null && A.length > 14;
      @*/
    public int[] throwAwayAssignmentToSingleField(int[] A, int x) {
        A[14] = x;
        
        //@ assignable \dl_hasTo(A[*]);
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { \abstract_statement P; }
        
        return A;
    }
}