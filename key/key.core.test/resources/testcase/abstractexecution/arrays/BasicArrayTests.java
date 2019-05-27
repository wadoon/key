public class BasicArrayTests {
    // The below example does *not* work if P may access A[14], since
    // then, it is depending on the value of x. Otherwise, we may discard
    // the assignmend, since P will overwrite it.
    /*@ public normal_behavior
      @ requires A != null && A.length > 14;
      @*/
    public Integer throwAwayAssignmentToSingleField(int[] A, int x) {
        A[14] = x;
        
        //@ assignable \dl_hasTo(A[*]);
        //@ accessible A[0..13], A[15..A.length-1];
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { \abstract_statement P; }
        
        return A[14];
    }
}