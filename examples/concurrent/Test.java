class Test extends Thread {

  int x;

  /*@ concurrent_behavior
    @ relies_on x == 0;
    @ guarantees false;
    @*/
}
