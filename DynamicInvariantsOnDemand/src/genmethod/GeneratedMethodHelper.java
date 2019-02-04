package genmethod;

import java.io.File;

import dynacode.DynaCode;

public final class GeneratedMethodHelper {
	private GeneratedMethodHelper() {
		
	}
	
	public static IGeneratedMethod getGeneratedMethod() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (IGeneratedMethod) dynacode.newProxyInstance(IGeneratedMethod.class,
				"genmethod.GeneratedMethod");
	}
}
