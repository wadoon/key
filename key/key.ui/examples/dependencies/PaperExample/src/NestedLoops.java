//public class NestedLoops {
//
//	
//	/*@ public normal_behavior
//	  @ requires \dl_noR(\dl_arrayRange(A,0,A.length-1)) && \dl_noW(\dl_arrayRange(A,0,A.length-1)) &&
//	  @ 		 \dl_noR(\dl_arrayRange(y,0,y.length-1)) && \dl_noW(\dl_arrayRange(y,0,y.length-1)) &&
//	  @ 		 \dl_noR(\dl_arrayRange(x,0,x.length-1)) && \dl_noW(\dl_arrayRange(x,0,x.length-1)) &&
//	  @  		 \dl_noR(\dl_arrayRange(tmp,0,tmp.length-1)) && \dl_noW(\dl_arrayRange(tmp,0,tmp.length-1)) &&
//	  @  		 
//	  @ ensures 
//	  @*/
//	public static void nestedLoops(int[] A, int[] y, int[] x, int[] tmp, int _PB_NY, int _PB_NX) {
//		int i =0;
//		int j = 0;
//		for (i = 0; i < _PB_NY; i++)
//		  y[i] = 0;
//		  for (i = 0; i < _PB_NX; i++)
//		    {
//		      tmp[i] = 0;
//		      for (j = 0; j < _PB_NY; j++)
//		    	  tmp[i] = tmp[i] + A[i][j] * x[j];
//		      for (j = 0; j < _PB_NY; j++)
//		    	  y[j] = y[j] + A[i][j] * tmp[i];
//		    }
//		}
//}
