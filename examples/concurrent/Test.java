class Test extends Thread {

  int x;

  /*@ concurrent_behavior
    @ requires target == this;
    @ requires x > 0;
    @ guarantees x > 0 && x > \prev(x);
    @ not_assigned \singleton(this.x);
    @ assignable \singleton(this.x);
    @*/

  public void run() { x *= 2; }
}
