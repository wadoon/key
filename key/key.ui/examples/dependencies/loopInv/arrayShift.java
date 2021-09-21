public class arrayShift{
	public int[] a;
	/*@public normal_behavior
	 @ requires \dl_noR(\dl_arrayRange(a,0,a.length-1)) && \dl_noW(\dl_arrayRange(a,0,a.length-1));
	 @ ensures \dl_noRaW(\dl_arrayRange(a,0,a.length-1));
	 @ diverges true;
	 @*/
	public void m() {
		int i=0;
		/*@ loop_invariant i>=0 && i < a.length-1 &&
		@ \dl_noRaW(\dl_arrayRange(a,0,a.length-1));
		@ decreases a.length - i;
		@ assignable a[0..a.length-2];
		@*/
		while(i < a.length - 1) {
			a[i]=a[i+1];
			i++;
		}
	}
}