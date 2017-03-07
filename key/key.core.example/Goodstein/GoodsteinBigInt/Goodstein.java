import java.io.*;
import java.math.BigInteger;

public class Goodstein{
  static BigInteger mIn;

  public static void goodsteinSequence(BigInteger startM){
     BigInteger base = BigInteger.ONE;
	        base = base.add(BigInteger.ONE);
     BigInteger m = startM;

    while   (m.compareTo(BigInteger.ZERO)>0) {
      m = nextExpand(m,base);
        if  (m.compareTo(BigInteger.ZERO)>0)
	  { m = m.subtract(BigInteger.ONE);}
        else {break;}
          base = base.add(BigInteger.ONE);}    
        }

   public static BigInteger nextExpand(BigInteger m, BigInteger oldBase){
      if (oldBase.compareTo(m) > 0)  {return m;}
      else {
 	BigInteger exp    = BigInteger.ZERO;
	BigInteger factor = BigInteger.ONE;
	BigInteger base   = oldBase;
 
    while (m.compareTo(factor.multiply(oldBase)) >= 0) {
       exp = exp.add(BigInteger.ONE);
       factor = factor.multiply(oldBase);}
       BigInteger[]  divArray = m.divideAndRemainder(factor);
       BigInteger r = intPow(oldBase.add(BigInteger.ONE),
                              nextExpand(exp,oldBase)).multiply(divArray[0]).add(nextExpand(divArray[1],oldBase));
       return r;}}
    
  public static BigInteger intPow(BigInteger base, BigInteger exp){
      BigInteger r = BigInteger.ONE;
      while (!exp.equals(BigInteger.ZERO)) {
	 r = r.multiply(base);
	 exp = exp.subtract(BigInteger.ONE);}
	return r;
      }

 public static void main(String[] args){
    int answer, startm, startb;
    int bunch = 0;
    System.out.println("Goodstein sequence for?"); 
     startm =   LiesInt(); 
     startb =  2; 
    BigInteger mIn = new BigInteger(String.valueOf(startm));
    BigInteger  base = new BigInteger(String.valueOf(startb));
    System.out.println("Goodstein sequence for " + mIn); 
    System.out.println(""); 

   while (mIn.compareTo(BigInteger.ZERO)!=0) {
	if (bunch == 0) {
    System.out.println("Continue n steps");
          answer  = LiesInt(); 
       if (answer == 0) {break;} 
       else { bunch = answer;}}
     System.out.print("Next Goodstein number " + mIn + "   "); 
     System.out.println("Base " + base); 
     mIn = nextExpand(mIn,base).subtract(BigInteger.ONE);
     base = base.add(BigInteger.ONE); 
     bunch = bunch -1;}
    }

 static int LiesInt() {
  DataInput StdEingabe = new DataInputStream(System.in);
  int ergebnis = 0;
    try{ ergebnis = Integer.parseInt(StdEingabe.readLine()); }
    catch (IOException io) {}
    return ergebnis;}
}
