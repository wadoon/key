class Test extends Thread {

  int x;

  /*@ concurrent_behavior
    @ relies_on x >= \prev(x);
    @ guarantees false;
    @*/
}
