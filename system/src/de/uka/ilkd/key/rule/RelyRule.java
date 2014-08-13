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
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.VariableReference;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
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
        final JavaBlock javaBlock = inst.target.javaBlock();
        final ExecutionContext ec = JavaTools.getInnermostExecutionContext(javaBlock, services);
        final KeYJavaType threadType = ec.getThreadTypeReference().getKeYJavaType();
        final ReferencePrefix thread = ec.getRuntimeThreadInstance();
        final ThreadSpecification ts = services.getSpecificationRepository().getThreadSpecification(threadType);
        if (ts == null) throw new RuleAbortException();
        final TermBuilder tb = services.getTermBuilder();
        
        final String excChoice = goal.proof().getSettings().getChoiceSettings().getDefaultChoice("runtimeExceptions");
        final boolean ignoreRTE = "runtimeExceptions:ignore".equals(excChoice);
        final boolean allowRTE = "runtimeExceptions:allow".equals(excChoice);
        assert ignoreRTE || allowRTE || "runtimeExceptions:ban".equals(excChoice);
        
        final Term threadVar = null; // TODO
        final Term heap = tb.getBaseHeap();
        final Term prevHeap = tb.getPrevHeap();
        final Term rely = ts.getRely(prevHeap, heap, threadVar, services);
        final Term notAssigned = ts.getNotChanged(threadVar, services);
        
        // PIO is possibly an update applied to a modality
        final Term leadingUpd = (app.pio.subTerm().op() instanceof UpdateApplication)?
                        app.pio.subTerm().sub(0): null;
        final Term target = leadingUpd == null? app.pio.subTerm(): app.pio.subTerm().sub(1);
        assert target == app.inst.target;
        
        final Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        final Term assigned = tb.setMinus(tb.allLocs(), notAssigned);
        final Term anonHeap = tb.func(new Function(new Name("anonHeap"), heapSort));
        final Term anonUpd = tb.elementary(heap, tb.anon(heap, assigned, anonHeap));
        final Term prevUpd = tb.parallel(tb.elementary(prevHeap, heap), anonUpd);
        final Term addRely = tb.apply(leadingUpd, tb.apply(prevUpd, rely));

        final Term post = target.sub(0);

        if (inst.emptyMod) { // empty modality rule
            final ImmutableList<Goal> res = goal.split(1);
            final Goal g = res.head();
            g.addFormula(new SequentFormula(addRely), true, false);
            final Term newPost = tb.apply(leadingUpd, tb.apply(anonUpd, post));
            g.changeFormula(new SequentFormula(newPost), app.pio);

            return res;
        } else { // read access
            ImmutableList<Goal> res;
            final JavaBlock newBlock = JavaTools.removeActiveStatement(javaBlock, services);
            final Term newProg = tb.prog((Modality)target.op(), newBlock, post);
            final Term assignUpd; // the particular assignment effect
            
            if (inst.fieldAccess != null) {
                // field (attribute) access
                
                if (ignoreRTE) res = goal.split(1);
                else {
                    // ban or allow RTE
                    res = goal.split(2);
                    assert false : "TODO";
                }

                assignUpd = null;
                // TODO

            } else {
                assert (inst.arrayAccess != null);
                // array access
                
                if (ignoreRTE) res = goal.split(1);
                else { // ban or allow RTE
                    res = goal.split(3);
                    assert false : "TODO";
                }

                assignUpd = null;
                // TODO
            }
            
            // add rely in any case
            final Goal aGoal = res.head();
            aGoal.addFormula(new SequentFormula(addRely), true, false);
            // assignment effect in any case
            final Term assignRes = tb.apply(leadingUpd, tb.apply(anonUpd, tb.apply(assignUpd, newProg)));
            aGoal.changeFormula(new SequentFormula(assignRes), app.pio);
            
            return res;
        }
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

        // must be applied on modality possibly with one update
        if (target.op() instanceof UpdateApplication)
            target = target.sub(1);
        
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
