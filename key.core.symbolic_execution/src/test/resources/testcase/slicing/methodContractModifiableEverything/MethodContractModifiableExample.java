
public class MethodContractModifiableExample {
   private static int x;

   private static int y;

   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static int main() {
     x = 2;
     y = 3;
     magic();
     return x;
   }

   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static void magic() {
   }
}
