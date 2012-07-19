package de.uka.ilkd.key.pp;

import java.io.Writer;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.pp.StringBackend;
import de.uka.ilkd.key.util.pp.WriterBackend;


public abstract class UIConfiguration {

	
	public UIConfiguration() {
		
	}
	
	public abstract ILogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, IServices services, boolean shortform);

	public abstract ILogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, WriterBackend backend, IServices services,
			boolean b);

	public abstract ILogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			INotationInfo notationInfo, StringBackend backend, IServices services,
			boolean b);

	public ILogicPrinter createLogicPrinter(ProgramPrinter programPrinter,
			StringBackend backend, IServices services, boolean shortform) {
		return createLogicPrinter(programPrinter, createDefaultNotationInfo(), backend, services, shortform);
	}

	public ILogicPrinter createLogicPrinter(INotationInfo notationInfo, IServices services) {
		return createLogicPrinter(createDefaultProgramPrinter(), notationInfo, services, false);
	}

	public ILogicPrinter createLogicPrinter() {
		return createLogicPrinter(createDefaultNotationInfo(), null);
	}

	public ILogicPrinter createLogicPrinter(INotationInfo info,
			StringBackend backend, IServices services, boolean shortform) {
		return createLogicPrinter(createDefaultProgramPrinter(), info, backend, services, shortform);
	}

	public ILogicPrinter createLogicPrinter(IServices services) {
		return createLogicPrinter(services, true);
	}

	public ILogicPrinter createLogicPrinter(IServices services, boolean b) {
		return createLogicPrinter(createDefaultProgramPrinter(), createDefaultNotationInfo(), services, b);
	}

	public ILogicPrinter createLogicPrinter(INotationInfo notInfo,
			IServices services, boolean b) {
		return createLogicPrinter(createDefaultProgramPrinter(), notInfo, services, b);
	}

	
	public abstract INotationInfo createDefaultNotationInfo();

	public abstract ProgramPrinter createDefaultProgramPrinter();

	public abstract ProgramPrinter createProgramPrinter(Writer writer,
			SVInstantiations svi);

	public abstract ProgramPrinter createProgramPrinter(Writer writer);



}
