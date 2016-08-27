package de.uka.ilkd.key.proof.init;

import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.IStatementBlock;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.visitor.IProgramContextAdder;
import de.uka.ilkd.key.java.visitor.IProgramReplaceVisitor;
import de.uka.ilkd.key.java.visitor.IProgramVariableCollector;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.java.visitor.ProgramContextAdder;
import de.uka.ilkd.key.java.visitor.ProgramReplaceVisitor;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.AbstractTacletSchemaVariableCollector;
import de.uka.ilkd.key.rule.TacletSchemaVariableCollector;
import de.uka.ilkd.key.rule.TacletVariableSVCollector;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.IReadPVCollector;
import de.uka.ilkd.key.util.IWrittenPVCollector;
import de.uka.ilkd.keyabs.abs.ABSCopyAssignment;
import de.uka.ilkd.keyabs.abs.ABSLocalVariableReference;
import de.uka.ilkd.keyabs.abs.ABSProgramContextAdder;
import de.uka.ilkd.keyabs.abs.ABSProgramReplaceVisitor;
import de.uka.ilkd.keyabs.abs.ABSProgramVariableCollector;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.ABSVariableDeclarationStatement;
import de.uka.ilkd.keyabs.abs.ABSVisitorImpl;
import de.uka.ilkd.keyabs.abs.IProgramASTModifyingVisitor;
import de.uka.ilkd.keyabs.proof.init.ABSProfile;
import de.uka.ilkd.keyabs.proof.init.ABSProgVarReplacer;
import de.uka.ilkd.keyabs.rule.ABSTacletSchemaVariableCollector;
import de.uka.ilkd.keyabs.rule.ABSTacletVariableSVCollector;

public class IProgramVisitorProvider {

    public static IProgramVisitorProvider INSTANCE = new IProgramVisitorProvider();

    public static IProgramVisitorProvider getInstance() {
        return INSTANCE;
    }

    public AbstractTacletSchemaVariableCollector createTacletSchemaVariableCollector() {
        return ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof ABSProfile ? new ABSTacletSchemaVariableCollector()
                : new TacletSchemaVariableCollector();
    }

    public AbstractTacletSchemaVariableCollector createTacletVariableSVCollector() {
        return ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof ABSProfile ? new ABSTacletVariableSVCollector()
                : new TacletVariableSVCollector();
    }

    public IReadPVCollector createReadPVCollector(ProgramElement root,
            IServices services) {
        return ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof ABSProfile ? new ABSReadPVCollector(
                root) : new ReadPVCollector(root, services);
    }

    public IWrittenPVCollector createWrittenPVCollector(ProgramElement root,
            IServices services) {
        return ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof ABSProfile ? new ABSWrittenPVCollector(
                root) : new WrittenPVCollector(root, services);
    }

    public IProgramReplaceVisitor createProgramReplaceVisitor(
            ProgramElement root, IServices services, SVInstantiations svInst,
            boolean allowPartialReplacement) {
        return ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof ABSProfile ? new ABSProgramReplaceVisitor(
                root, (ABSServices) services, svInst, allowPartialReplacement)
                : new ProgramReplaceVisitor(root, services, svInst,
                        allowPartialReplacement);
    }

    public IProgramVariableCollector<LocationVariable> createProgramVariableCollector(
            ProgramElement root, IServices services) {
        return ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof ABSProfile ?
                new ABSProgramVariableCollector( root, (ABSServices) services) :
                new ProgramVariableCollector(root, services);
    }

    private static final class ABSReadPVCollector extends ABSVisitorImpl
            implements IReadPVCollector {
        private ImmutableSet<ProgramVariable> result = DefaultImmutableSet
                .<ProgramVariable> nil();

        private ImmutableSet<ProgramVariable> declaredPVs = DefaultImmutableSet
                .<ProgramVariable> nil();

        public ABSReadPVCollector(ProgramElement root) {
            super(root);
        }

        @Override
        protected void doDefaultAction(ProgramElement node) {
            if (node instanceof ProgramVariable) {
                ProgramVariable pv = (ProgramVariable) node;
                if (!pv.isMember() && !declaredPVs.contains(pv)) {
                    result = result.add(pv);
                }
            }
        }

        public ImmutableSet<ProgramVariable> result() {
            return result;
        }
    }

    private static final class ABSWrittenPVCollector extends ABSVisitorImpl
            implements IWrittenPVCollector {
        private ImmutableSet<ProgramVariable> result = DefaultImmutableSet
                .<ProgramVariable> nil();

        private ImmutableSet<ProgramVariable> declaredPVs = DefaultImmutableSet
                .<ProgramVariable> nil();

        public ABSWrittenPVCollector(ProgramElement root) {
            super(root);
        }

        @Override
        protected void doDefaultAction(ProgramElement node) {
            if (node instanceof ABSCopyAssignment) {
                ProgramElement lhs = ((ABSCopyAssignment) node).getChildAt(0);
                if (lhs instanceof ABSLocalVariableReference) {
                    ProgramVariable pv = (ProgramVariable) ((ABSLocalVariableReference) lhs).getProgramVariable();
                    if (!declaredPVs.contains(pv)) {
                        result = result.add(pv);
                    }
                }
            } else if (node instanceof ABSVariableDeclarationStatement) {
                ProgramVariable pv = (ProgramVariable) ((ABSVariableDeclarationStatement) node)
                        .getVariable();
                if (!pv.isMember()) {
                    assert !declaredPVs.contains(pv);
                    assert !result.contains(pv);
                    declaredPVs = declaredPVs.add(pv);
                }
            }
        }

        public ImmutableSet<ProgramVariable> result() {
            return result;
        }
    }

    private static final class ReadPVCollector extends JavaASTVisitor implements
            IReadPVCollector {
        private ImmutableSet<ProgramVariable> result = DefaultImmutableSet
                .<ProgramVariable> nil();

        private ImmutableSet<ProgramVariable> declaredPVs = DefaultImmutableSet
                .<ProgramVariable> nil();

        public ReadPVCollector(ProgramElement root, IServices services) {
            super(root, services);
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if (node instanceof ProgramVariable) {
                ProgramVariable pv = (ProgramVariable) node;
                if (!pv.isMember() && !declaredPVs.contains(pv)) {
                    result = result.add(pv);
                }
            }
        }

        public ImmutableSet<ProgramVariable> result() {
            return result;
        }
    }

    private static final class WrittenPVCollector extends JavaASTVisitor
            implements IWrittenPVCollector {
        private ImmutableSet<ProgramVariable> result = DefaultImmutableSet
                .<ProgramVariable> nil();

        private ImmutableSet<ProgramVariable> declaredPVs = DefaultImmutableSet
                .<ProgramVariable> nil();

        public WrittenPVCollector(ProgramElement root, IServices services) {
            super(root, services);
        }

        @Override
        protected void doDefaultAction(SourceElement node) {
            if (node instanceof Assignment) {
                ProgramElement lhs = ((Assignment) node).getChildAt(0);
                if (lhs instanceof ProgramVariable) {
                    ProgramVariable pv = (ProgramVariable) lhs;
                    if (!pv.isMember() && !declaredPVs.contains(pv)) {
                        result = result.add(pv);
                    }
                }
            } else if (node instanceof VariableSpecification) {
                VariableSpecification vs = (VariableSpecification) node;
                ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
                if (!pv.isMember()) {
                    assert !declaredPVs.contains(pv);
                    assert !result.contains(pv);
                    declaredPVs = declaredPVs.add(pv);
                }
            }
        }

        public ImmutableSet<ProgramVariable> result() {
            return result;
        }
    }

    public static IProgramASTModifyingVisitor createProgVarReplaceVisitor(ProgramElement pe,
            Map<ProgramVariable, ProgramVariable> map, boolean replaceAll,
            IServices services) {
        return ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof ABSProfile ? new ABSProgVarReplacer(pe, map, false) :
            new ProgVarReplaceVisitor(pe, map, false, services);
    }

	public static <E extends IStatementBlock> IProgramContextAdder<E> createProgramContextAdder() {
		 return (IProgramContextAdder<E>) (ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof ABSProfile ? ABSProgramContextAdder.INSTANCE : ProgramContextAdder.INSTANCE); 
	}
}
