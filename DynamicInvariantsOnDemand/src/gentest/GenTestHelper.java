package gentest;

import dynacode.DynaCode;
import java.io.File;

public final class GenTestHelper {
	private GenTestHelper() {
			
	}
	
	public static IGenTest getGeneratedTest() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (IGenTest) dynacode.newProxyInstance(IGenTest.class,
				"gentest.GenTest");
	}
}