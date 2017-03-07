

public class Goodstein{

      /*@ normal_behavior
        @  requires startM > 0;
        @*/
      public void GoodsteinSequence(int startM){
	  int base = 2;
          int m = startM;

        /*@ loop_invariant
          @  m >= 0 & base >= 2;
          @
          @  assignable \strictly_nothing;
          @  decreases \dl_oGS(base,m);
          @*/
	  while   (m > 0) {
	      m = nextExpand(m,base);
              if (m>0) {m = m-1;}
              else {break;}
              base = base+1;
	  }    
        }

      /*@ normal_behavior
        @ requires m >= 0;
        @ requires oldBase >= 2;
        @ ensures \result >= 0;
        @ ensures \result ==  \dl_oHNf(oldBase,m);
        @ ensures \dl_oGS(oldBase,m) == \dl_oGS(oldBase+1,\result);
        @  assignable \strictly_nothing;
        @ measured_by m;
        @*/
    public int nextExpand(int m, int oldBase){

        if (oldBase > m) { return m;}
	else {

	int exp = 0;
        int factor = 1;
        int base = oldBase;

 
      /*@ normal_behavior
	@ ensures m >=  intPow(oldBase,exp);
        @ ensures m <   intPow(oldBase,exp + 1);
        @ ensures factor > 0  & factor == intPow(oldBase,exp) ;
        @ ensures exp  >=  0 ;
        @ 
        @ assignable \strictly_nothing;
        @*/
	{
  
      /*@ loop_invariant
          @  factor == intPow(oldBase,exp) &
          @  exp >= 0 &
          @  m >= factor &
          @  factor > 0;
          @
          @  assignable \strictly_nothing;
          @  decreases (m - factor);
          @*/
    while (m >= factor*oldBase) {
                               exp = exp+1; factor = factor * oldBase;
                              } 
	};
      

	int a = 1;
        int c = 0;

     /*@ normal_behavior
	@ ensures m == \dl_pow(oldBase, exp) * a + c & 
        @ 2<=oldBase  & 1<=exp  &   0 < a & a < oldBase  & c < \dl_pow(oldBase,exp) & c >= 0;
        @ 
        @ assignable \strictly_nothing;
        @*/
	{
	    a =  m/factor;
            c = m - factor*a;
        };

	int r = intPow(oldBase+1,nextExpand(exp,oldBase))*a;
	r = r + nextExpand(c,oldBase);
	

	return r;
	
	}
    }
    
 
      /*@ normal_behaviour
        @ requires base >= 0;
        @ requires exp  >= 0;
        @ ensures \result == \dl_pow(base,exp);
        @*/
    public static int  /*@ \strictly_pure @*/ intPow(int base, int exp){
        int r = 1;
        
        /*@ loop_invariant
          @  r == \dl_pow(base,\old(exp)-exp) &
          @  \old(exp) >= exp & 
          @  exp >= 0;
          @  assignable \strictly_nothing;
          @  decreases exp+1;
          @*/

	while (exp != 0) {
	    r = r*base;
	exp--;
    }
	return r;
    }

}
