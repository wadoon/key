/** Example adapted from Smans et al.: Shared Boxes
  *
  */
final class Client extends Thread {


  /*@ concurrent_behavior
    @ requires target instanceof Client;
    @ relies_on Inc.X >= \prev(Inc.X);
    @ assignable \strictly_nothing;
    @*/

    public void run() { check(); }

    //@ ensures \result;
    boolean check() {
        int m = Inc.X;
        int n = Inc.X;
        return m <= n;
    }
}
