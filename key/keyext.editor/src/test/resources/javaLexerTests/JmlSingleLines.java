class JmlSingleLines {
    //@ ensures true;
    public void test() {}

    //@ requires f(a);
    public void test() {}

    //@ requires_free f(a);
    public void test() {}

    //@ assignable f(a);
    public void test() {}

    //@ assignable missing_semicolon
    public void test() {}

    //@ requires \nothing;
    //@ ensures \everything;
    public void test() {}

    /* This is a comment:
        //@ ensures \everything;
        So the previous jml contract should not be lexed.
     */
    //@ requires_free blubb;
}