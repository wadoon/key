public class MaxIntBuggy {
   private int content;
   private int arr[];
   
   //@ public static ghost boolean tc1;
   //@ public static ghost boolean tc2;
   //@ public static ghost boolean tc3;
   //@ public static ghost boolean tc4;
   //@ public static ghost boolean tc5;
   //@ public static ghost boolean tc6;
   //@ public static ghost boolean tc7;
   //@ public static ghost boolean tc8;
   //@ public static ghost boolean tc9;
   //@ public static ghost boolean tc0;

   
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
