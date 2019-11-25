package de.uka.ilkd.key.rule;

import java.util.List;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.BlockContractImpl;

/**
 * Application of {@link AbstractBlockContractRule}.
 *
 * @author wacker, lanzinger
 */
public abstract class AbstractBlockContractBuiltInRuleApp
        extends AbstractAuxiliaryContractBuiltInRuleApp {

    /**
     * @see #getContract()
     */
    protected BlockContract contract;
    
    protected boolean representsJMLAssumeStmt = false;

    /**
     *
     * @param rule
     *            the rule being applied.
     * @param occurrence
     *            the position at which the rule is applied.
     * @param ifInstantiations
     *            if instantiations.
     */
    public AbstractBlockContractBuiltInRuleApp(BuiltInRule rule, PosInOccurrence occurrence,
            ImmutableList<PosInOccurrence> ifInstantiations) {
        super(rule, occurrence, ifInstantiations);
    }

    @Override
    public BlockContract getContract() {
        return contract;
    }

    /**
     *
     * @param goal
     *            the current goal.
     * @param rule
     *            the rule being applied.
     * @return this.
     */
    public AbstractBlockContractBuiltInRuleApp tryToInstantiate(final Goal goal,
            final AbstractBlockContractRule rule) {
        if (complete() || cannotComplete(goal)) {
            return this;
        }
        final Services services = goal.proof().getServices();
        final AbstractBlockContractRule.Instantiation instantiation = rule
                .instantiate(posInOccurrence().subTerm(), goal, services);
        final ImmutableSet<BlockContract> contracts = AbstractBlockContractRule
                .getApplicableContracts(instantiation, goal, services);
        setStatement(instantiation.statement);
        ImmutableSet<BlockContract> cons = DefaultImmutableSet.<BlockContract> nil();
        for (BlockContract cont : contracts) {
            if (cont.getBlock().getStartPosition().getLine() == getStatement().getStartPosition()
                    .getLine()) {
                cons = cons.add(cont);
            }
        }
        contract = BlockContractImpl.combine(cons, goal.getLocalSpecificationRepository(), services);
        heaps = HeapContext.getModHeaps(services, instantiation.isTransactional());
        
        /**
         * This flag is true if we could detect that the "contract" is a translation
         * from a JML assume clause. Yeah, that's one of these hacks,
         * but using block contracts for everything also is a hack. (DS, 2019-11-20)
         * 
         * NOTE (DS, 2019-11-20): There's a similar hack on which this one depends in
         * AbstractAuxiliaryContractImpl, it prevents creating "standard" preconditions. 
         */
        representsJMLAssumeStmt = (contract.getBlock().isEmpty()
                || contract.getBlock().toString().replaceAll(" ", "").equals("{;}"))
                && heaps.stream().map(heap -> contract.getPrecondition(heap, services))
                        .allMatch(t -> t == null || t.equals(services.getTermBuilder().tt()));
        
        return this;
    }

    /**
     *
     * @param statement
     *            the new statement.
     * @param contract
     *            the new contract.
     * @param heaps
     *            the new heap context.
     */
    public void update(final JavaStatement statement, final BlockContract contract,
            final List<LocationVariable> heaps) {
        setStatement(statement);
        this.contract = contract;
        this.heaps = heaps;
    }
}
