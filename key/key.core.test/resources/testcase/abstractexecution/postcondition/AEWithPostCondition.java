public class AEWithPostCondition {
    /*@ public normal_behavior
      @ requires input >= 0;
      @ ensures \result == input * input;
      @*/
    public int square(int input) {
        int x = 0;
        int i = 0;

        /*@ loop_invariant x == i * input && i >= 0 && i <= input;
          @ decreases input - i;
          @*/
        while (i < input) {
            x += input;
            i++;
        }

        return x;
    }
    
    /*@ public normal_behavior
      @ requires input >= 0;
      @ ensures \result == input * input;
      @*/
    public int squareAbstrStep0(int input) {
        int x = 0;

        //@ declares \dl_localsP1;
        //@ accessible input, x, \dl_localsP1;
        //@ assignable x, \dl_localsP1;
        //@
        //@ normal_behavior ensures x == input * input;
        //@ exceptional_behavior requires false;
        //@ return_behavior requires false;
        { \abstract_statement P1; }

        return x;
    }
    
    /*@ public normal_behavior
      @ requires input >= 0;
      @ ensures \result == input * input;
      @*/
    public int squareAbstrStep1(int input) {
        int x = 0;
        int i = 0;

        //@ accessible input, x, i;
        //@ assignable \hasTo(x), \hasTo(i);
        //@
        //@ normal_behavior ensures x == input * input && i == input;
        //@ exceptional_behavior requires false;
        //@ return_behavior requires false;
        { \abstract_statement P2; }

        return x;
    }
    
    /*@ public normal_behavior
      @ requires input >= 0;
      @ ensures \result == input * input;
      @*/
    public int squareAbstrStep2(int input) {
        int x = 0;
        int i = 0;

        /*@ loop_invariant x == i * input && i >= 0 && i <= input;
          @ decreases input - i;
          @*/
        while (i < input) {
            //@ ghost int oldX = x;
            //@ ghost int oldI = i;
            
            //@ accessible input, x, i;
            //@ assignable \hasTo(x), \hasTo(i);
            //@
            //@ normal_behavior ensures x == oldX + input && i == oldI + 1;
            //@ exceptional_behavior requires false;
            //@ return_behavior requires false;
            //@ break_behavior requires false;
            //@ continue_behavior requires false;
            { \abstract_statement P3; }
        }

        return x;
    }
}