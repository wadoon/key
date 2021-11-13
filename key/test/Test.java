class Test {
    //@requires 0 <= x <= 10;
    //@requires 0 <= y <= 10;
    //@ensures \result >= 0 ;
    public int foo(int x, int y) {
        int z = x + y;
        return z;
    }
}