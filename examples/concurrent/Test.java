class Test extends Thread {

  int x;

  /*@ concurrent_behavior
    @ requires x >= 0;
    @ relies_on x >= \prev(x);
    @ guarantees false;
    @*/
}
