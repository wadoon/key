package com.csvanefalk.keytestgen.targetmodels.loops.dowhile;

public class DoWhileFalseTest {
    /*@ requires true;
      @ ensures true;
      @*/
    public int main() {
        int result = 0;
        do {
            result++;
        }
        while (false);
        return result;
    }
}
