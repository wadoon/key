public class MaxIntBuggy {
	static int arr[];

	// tc "test case"
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

	// Alternative:
	// arbitrary many tcX by setting tc = X
	//@ public static ghost int tc;
	//@ public static ghost int run;

	public static int max() {
		int m = arr[0];
		for (int k=0; k < arr.length; k++) {
			if ( m < arr [k]) {
				m = arr[k++];
			}
		}
		return m;
	}


	public static int max(int arr[]) {
		int m = arr[0];
		for (int k=0; k < arr.length; k++) {
			if ( m < arr [k]) {
				m = arr[k++];
			}
		}
		return m;
	}

	public static int sum(int arr[]) {
		int m = arr[0];
		for (int k=0; k < arr.length; k++) {
			m += arr[++k];
		}
		return m;
	}
}
