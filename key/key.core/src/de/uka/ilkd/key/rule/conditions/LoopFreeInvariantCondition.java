package de.uka.ilkd.key.rule.conditions;

import java.util.Optional;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

/**
 * TODO
 * 
 * @author Dominic Steinhoefel
 */
public class LoopFreeInvariantCondition implements VariableCondition {
    private final SchemaVariable inv;
    private final SchemaVariable modalitySV;

    public LoopFreeInvariantCondition(SchemaVariable inv,
            SchemaVariable modality) {
        this.inv = inv;
        this.modalitySV = modality;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();
        final TermBuilder tb = services.getTermBuilder();

        if (svInst.getInstantiation(inv) != null) {
            return matchCond;
        }

        final Modality modality = (Modality) svInst
                .getInstantiation(modalitySV);

        final JavaBlock javaBlock = JavaBlock
                .createJavaBlock((StatementBlock) svInst
                        .getContextInstantiation().contextProgram());

        final MethodFrame mf = //
                JavaTools.getInnermostMethodFrame(javaBlock, services);
        final Term selfTerm = Optional.ofNullable(mf).map(
                methodFrame -> MiscTools.getSelfTerm(methodFrame, services))
                .orElse(null);

        final LoopStatement loop = (LoopStatement) JavaTools
                .getActiveStatement(javaBlock);
        final LoopSpecification loopSpec = //
                services.getSpecificationRepository().getLoopSpec(loop);

        if (loopSpec == null) {
            return null;
        }

        Term freeInvInst = tb.tt();
        for (final LocationVariable heap : MiscTools
                .applicableHeapContexts(modality, services)) {
            final Term currentFreeInvInst = freeInvInst;

            final Optional<Term> maybeFreeInvInst = Optional
                    .ofNullable(loopSpec.getFreeInvariant(heap, selfTerm,
                            loopSpec.getInternalAtPres(), services));

            freeInvInst = maybeFreeInvInst
                    .map(inv -> tb.and(currentFreeInvInst, inv))
                    .orElse(freeInvInst);
        }

        return matchCond.setInstantiations( //
                svInst.add(inv, freeInvInst, services));
    }

    @Override
    public String toString() {
        return "\\getFreeInvariant(" + inv + ", " + modalitySV + ")";
    }
}
