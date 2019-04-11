package de.uka.ilkd.key.rule.conditions;

import java.util.Optional;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
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
public class HasLoopInvariantCondition implements VariableCondition {
    private final SchemaVariable modalitySV;

    public HasLoopInvariantCondition(SchemaVariable modality) {
        this.modalitySV = modality;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

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

        boolean hasInv = false;
        for (final LocationVariable heap : MiscTools
                .applicableHeapContexts(modality, services)) {
            final Optional<Term> maybeInvInst = Optional
                    .ofNullable(loopSpec.getInvariant(heap, selfTerm,
                            loopSpec.getInternalAtPres(), services));
            final Optional<Term> maybeFreeInvInst = Optional
                    .ofNullable(loopSpec.getFreeInvariant(heap, selfTerm,
                            loopSpec.getInternalAtPres(), services));

            hasInv |= maybeInvInst.isPresent();
            hasInv |= maybeFreeInvInst.isPresent();
        }

        return hasInv ? matchCond : null;
    }

    @Override
    public String toString() {
        return "\\hasInvariant(" + modalitySV + ")";
    }
}