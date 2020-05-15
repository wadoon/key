public class MaxIntBuggy {
   private int content;
   private int arr[];

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
