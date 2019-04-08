package geninstrument;

import java.io.File;

import dynacode.DynaCode;

public final class GenInstrumentHelper {
	private GenInstrumentHelper() {
		
	}
	
	public static IGenInstrument getGenInstrument() {
		DynaCode dynacode = new DynaCode();
		dynacode.addSourceDir(new File("dynacode"));
		return (IGenInstrument) dynacode.newProxyInstance(IGenInstrument.class,
				"geninstrument.GenInstrument");
	}
}
