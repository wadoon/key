class Test2 {
    // ensures_free bar(x)==\result;
    //@ ensures \result>x;
    int bar (int x) {
        return x+1;
    }

    //@ ensures \result > 42;
    int foo(int x) {
        return bar(x);
    }
}