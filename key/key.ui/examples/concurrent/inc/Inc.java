/** Example adapted from Smans et al.: Shared Boxes
  *
  */
final class Inc extends Thread {

    static int X;

  /*@ concurrent_behavior
    @ requires target == this;
    @ guarantees X > \prev(X);
    @ not_assigned X;
    @ assignable X;
    @*/

    public void run() {
        while (true) { X++; }
    }
}
