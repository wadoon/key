package de.uka.ilkd.keyabs.pp;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.pp.ILogicPrinter;
import de.uka.ilkd.key.pp.INotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.UIConfiguration;
import de.uka.ilkd.key.util.pp.StringBackend;
import de.uka.ilkd.key.util.pp.WriterBackend;

public class ABSUIConfiguration extends UIConfiguration {

	@Override
	public ILogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, IServices services) {
		return new LogicPrinter(programPrinter, notationInfo, services);
	}

	@Override
	public ILogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, IServices services, boolean pureprint) {
		return new LogicPrinter(programPrinter, notationInfo, services, pureprint);
	}

	@Override
	public ILogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, StringBackend backend,
			IServices services, boolean b) {
		return new LogicPrinter(programPrinter, notationInfo, backend, services, b);
	}

	@Override
	public ILogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, WriterBackend backend, Object services,
			boolean b) {
		return new LogicPrinter(programPrinter, notationInfo, backend, services, b);
	}

}
