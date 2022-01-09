public class Test {
    //@ ghost \locset l1;
    //@ ghost \locset l2;
    //@ ghost \locset l3;

    //@ requires true;
    //@ ensures l1 <= l3;
    public void foo() {
        //@ set l1 = l3 - l2;
        //@ set l3 = l3 + l1 + l2;
        return;
    }
}