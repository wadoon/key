package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.util.pp.StringBackend;
import de.uka.ilkd.key.util.pp.WriterBackend;


public abstract class UIConfiguration {

	public UIConfiguration() {
		
	}
	
	public abstract LogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, IServices services);	

	public abstract LogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, IServices services, boolean shortform);

	public abstract LogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, StringBackend backend,
			IServices services, boolean b);

	public abstract LogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, WriterBackend backend, Object services,
			boolean b);
	
}
