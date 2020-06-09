public class MaxIntBuggy {
   private int content;
   private int arr[];
   
   //@ public ghost boolean tc1;
   //@ public ghost boolean tc2;
   //@ public ghost boolean tc3;
   //@ public ghost boolean tc4;
   //@ public ghost boolean tc5;
   //@ public ghost boolean tc6;
   //@ public ghost boolean tc7;
   //@ public ghost boolean tc8;
   //@ public ghost boolean tc9;
   //@ public ghost boolean tc0;

   
   public boolean contentEqualsMax() {
      if (max(arr) == content) {
         return true;
      }
      else {
         return false;
      }
   }
   
   public int max() {
      int m = arr[0];
      for (int k=0; k < arr.length; k++) {
         if ( m < arr [k]) {
            m = arr[++k];
         }
      }
      return m;
   }

   public static int max(int arr[]) {
      int m = arr[0];
      for (int k=0; k < arr.length; k++) {
         if ( m < arr [k]) {
            m = arr[++k];
         }
      }
      return m;
   }
}
