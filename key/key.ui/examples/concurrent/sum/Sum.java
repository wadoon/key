import edu.kit.iti.concurrent.Lock;

final class Sum extends Thread {

    static int S;
    static int[] A;
    //@ static ghost boolean[] C;

    int id;

    /*@ concurrent_behavior
      @ requires target == this;
      @ requires !C[id];
      @ requires A.length == C.length;
      @ requires 0 <= id && id < A.length;
      @ guarantees S == (\sum int k; 0 <= k && k < A.length; C[k]? A[k]: 0)
      @     && Lock.holder != this ==> S == \prev(S);
      @ relies_on S == (\sum int k; 0 <= k && k < A.length; C[k]? A[k]: 0)
      @     && Lock.holder == this ==> S == \prev(S);
      @ assignable S, A[id], C[id];
      @ not_assigned A[id], C[id];
      @*/
    public void run () {
        Lock.lock(this);
        S += A[id];
        //@ set C[id] = true;
        Lock.unlock(this);
    }
}
