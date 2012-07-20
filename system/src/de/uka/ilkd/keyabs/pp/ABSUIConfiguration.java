package de.uka.ilkd.keyabs.pp;

import java.io.Writer;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.pp.ILogicPrinter;
import de.uka.ilkd.key.pp.INotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.UIConfiguration;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.pp.StringBackend;
import de.uka.ilkd.key.util.pp.WriterBackend;

public class ABSUIConfiguration extends UIConfiguration {

	@Override
	public INotationInfo createDefaultNotationInfo() {
		return new NotationInfo();
	}

	@Override
	public ProgramPrinter createDefaultProgramPrinter() {
		return null;
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
			INotationInfo notationInfo, WriterBackend backend, IServices services,
			boolean b) {
		return new LogicPrinter(programPrinter, notationInfo, backend, services, b);
	}

	@Override
	public ProgramPrinter createProgramPrinter(Writer writer) {
		return null;
	}

	@Override
	public ProgramPrinter createProgramPrinter(Writer writer, SVInstantiations svi) {
		return null;
	}

}
