package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.VariableReference;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.ThreadSpecification;

/**
 * Rule to handle heap read access in concurrent programs
 * using rely/guarantee contracts.
 * @author bruns
 *
 */
public final class RelyRule implements BuiltInRule {
    
    public final static RelyRule INSTANCE = new RelyRule();
    private static final Name NAME = new Name("Rely");
    
    private Term lastFocusTerm;
    private Instantiation lastInstantiation;

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
                    RuleApp ruleApp) throws RuleAbortException {
        if (!( ruleApp instanceof RelyBuiltInRuleApp))
                        throw new RuleAbortException();
        final RelyBuiltInRuleApp app = (RelyBuiltInRuleApp) ruleApp;
        final Instantiation inst = app.inst;
        if (inst == null) throw new RuleAbortException();
        final ThreadSpecification ts = getApplicableThreadSpec(inst.target.javaBlock(), services);
        if (ts == null) throw new RuleAbortException();
        // todo Auto-generated method stub
        return null;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return name().toString();
    }
    
    @Override
    public String toString() {
        return displayName();
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null || pio.isInAntec() || !pio.isTopLevel()) return false;
        final Services services = goal.proof().getServices();
        // check whether rely/guarantee option is set
        if (!relyGuaranteeEnabled(goal)) return false;
        final Term target = pio.constrainedFormula().formula();
        final Instantiation inst = getInstantiation(target, goal);
        lastFocusTerm = target;
        lastInstantiation = inst;
        if (inst == null) return false;
        return getApplicableThreadSpec(inst.target.javaBlock(), services) != null;
    }

    private boolean relyGuaranteeEnabled(Goal goal) {
        final String concurrenyChoice = goal.proof().getSettings().getChoiceSettings().getDefaultChoice("concurrency");
        return "concurrency:RG".equals(concurrenyChoice);
    }
    
    Instantiation getInstantiation(Term target, Goal goal) {
        if (target == lastFocusTerm) return lastInstantiation;
        
        while (target.op() instanceof UpdateApplication) {
            target = UpdateApplication.getTarget(target);
        }
        if (!(target.op() instanceof Modality)) return null;
        final JavaBlock prog = target.javaBlock();
        final SourceElement activeStm = JavaTools.getActiveStatement(prog);
        if (activeStm == null) {
            // empty modality
            return new Instantiation(target);
        }
        if (!(activeStm instanceof Assignment)) return null;
        final Expression lhs = ((Assignment) activeStm).getLhs();
        
        // investigate RHS
        final Expression rhs = ((Assignment) activeStm).getRhs();
        // must be field access (excludes array length)
        if (rhs instanceof FieldReference) {
            assert lhs instanceof ProgramVariable: "unexpected: "+lhs;
            final ProgramVariable field = ((FieldReference) rhs).getProgramVariable();
            // must not be final
            if (field.isFinal()) return null;

            // prefix may still be this, static access (w/ variable prefix)
            return new Instantiation(target, (ProgramVariable) lhs, (FieldReference) rhs); // TODO
        } else if (rhs instanceof ArrayReference) {
            assert lhs instanceof ProgramVariable: "unexpected: "+lhs;
            return new Instantiation(target, (ProgramVariable) lhs, (ArrayReference) rhs);
        } else
            return null;
    }
    
    private static ThreadSpecification getApplicableThreadSpec(JavaBlock jb, Services services) {
        final ExecutionContext ec = JavaTools.getInnermostExecutionContext(jb, services);
        final KeYJavaType threadType = ec.getThreadTypeReference().getKeYJavaType();
        return services.getSpecificationRepository().getThreadSpecification(threadType);
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new RelyBuiltInRuleApp(this, pos);
    }
    
    static class Instantiation {
        
        final Term target;
        final boolean emptyMod;
        final ProgramVariable lhs;
        final FieldReference fieldAccess;
        final ArrayReference arrayAccess;
        
        private Instantiation (Term target) {
            this.target = target;
            assert target.javaBlock() != null;
            emptyMod = true;
            lhs = null;
            fieldAccess = null;
            arrayAccess = null;
        }
        
        private Instantiation (Term target, ProgramVariable lhs, FieldReference fr) {
            this.target = target;
            assert target.javaBlock() != null;
            emptyMod = false;
            this.lhs = lhs;
            fieldAccess = fr;
            arrayAccess = null;
        }
        
        private Instantiation (Term target, ProgramVariable lhs, ArrayReference ar) {
            this.target = target;
            assert target.javaBlock() != null;
            emptyMod = false;
            this.lhs = lhs;
            fieldAccess = null;
            arrayAccess = ar;
        }
    }

}
