package de.uka.ilkd.key.strategy.conflictbasedinst;

public class Tester {

    public static void main(String args[]) {
       long a = 0;
       long old_a = a;
       long ts = System.currentTimeMillis();
       while(true) {
           old_a = a;
           a++;
           if(old_a > a) {
               System.out.println("OVERFLOW: a=" + a + ", old_a = " + old_a);
               break;
           }
       }
       ts = System.currentTimeMillis() - ts;
       System.out.println("This took " + ts + " ms");

    }
}
