import edu.kit.iti.concurrent.Lock;

final class Sum extends Thread {

    static int S;
    int A;
    //@ ghost boolean C;

    /*@ concurrent_behavior
      @ requires target == this;
      @ requires !C;
      @ guarantees Lock.holder == this ==> S == (\prev(S)+A)
      @     && Lock.holder != this ==> S == \prev(S);
      @ relies_on Lock.holder == this ==> S == \prev(S);
      @ assignable S, C;
      @ not_assigned A, C;
      @*/
    public void run () {
        Lock.lock(this);
        S += A;
        //@ set C = true;
        Lock.unlock(this);
    }
}
