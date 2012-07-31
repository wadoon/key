package de.uka.ilkd.key.pp;

import java.io.Writer;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.pp.StringBackend;
import de.uka.ilkd.key.util.pp.WriterBackend;

public class JavaUIConfiguration extends UIConfiguration {

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
	public INotationInfo createDefaultNotationInfo() {
		return new NotationInfo();
	}

	@Override
	public ProgramPrinter createDefaultProgramPrinter() {
		return new ProgramPrinter();
	}

	@Override
	public ProgramPrinter createProgramPrinter(Writer writer, SVInstantiations svi) {
		return new ProgramPrinter(writer, svi);
	}

	@Override
	public ProgramPrinter createProgramPrinter(Writer writer) {
		return new ProgramPrinter(writer);
	}



}
