public class TestAEHeap {
    private int field1;
    private int field2;
   
    /*@ public normal_behavior
      @ ensures field2 == 42;
      @*/
    public void test1() {
        field1 = 17;
        field2 = 42;
       
        //@ assignable this.field1;
        //@ accessible this.field1, this.field2;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { abstract_statement P; }
       
        return;
    }
   
    /*@ public normal_behavior
      @ ensures field1 == 17; // not true
      @*/
    public void test2() {
        field1 = 17;
        field2 = 42;
       
        //@ assignable this.field1;
        //@ accessible this.field1, this.field2;
        //@ return_behavior requires false;
        //@ exceptional_behavior requires false;
        { abstract_statement P; }
       
        return;
    }
}