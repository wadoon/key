// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.rule.metaconstruct;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.abstractexecution.java.AbstractProgramElement;
import de.uka.ilkd.key.abstractexecution.logic.op.AbstractUpdateFactory.PreconditionType;
import de.uka.ilkd.key.abstractexecution.logic.op.locs.AbstractUpdateLoc;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionContractUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.mgt.GoalLocalSpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Transformer creating abstract preconditions for various completion behaviors.
 * Operators (functions) used for such preconditions are created "fresh for" an
 * APE identifier symbol.
 * 
 * @author Dominic Steinhoefel
 */
public class AbstractPreconditionTransformer extends AbstractTermTransformer {
    private static final Name NAME = new Name("#abstrPrecond");

    public AbstractPreconditionTransformer() {
        super(NAME, 2);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            GoalLocalSpecificationRepository localSpecRepo, Services services) {
        final AbstractProgramElement ape = getAPE(term, svInst);

        final Optional<ExecutionContext> executionContext = Optional
                .ofNullable(svInst.getExecutionContext());

        assert term.subs().size() == 2;
        final PreconditionType preconditionType = getPreconditionType(term.sub(1), services);

        final List<AbstractUpdateLoc> accessibles = //
                AbstractExecutionContractUtils.getAccessibleAndAssignableTermsForNoBehaviorContract(
                        ape, Optional.empty(), localSpecRepo, services, executionContext).first;

        final ImmutableArray<Term> accessiblesTerms = accessibles.stream()
                .map(loc -> loc.toTerm(services)).collect(ImmutableArray.toImmutableArray());
        final Sort[] accessibleSorts = accessibles.stream().map(AbstractUpdateLoc::sort)
                .collect(Collectors.toList()).toArray(new Sort[0]);

        final Function precondFun = services.abstractUpdateFactory()
                .getAbstractPreconditionInstance(ape, preconditionType, accessibleSorts);

        return services.getTermFactory().createTerm(precondFun, accessiblesTerms, null, null);
    }

    public static PreconditionType getPreconditionType(Term term, Services services) {
        final CharListLDT charListLDT = services.getTypeConverter().getCharListLDT();
        final SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();
        assert term.op() instanceof Function;
        assert seqLDT.containsFunction((Function) term.op());

        final String completionType = //
                charListLDT.translateTerm(term, null, services).toString().replace("\"", "");
        return Arrays.stream(PreconditionType.values())
                .filter(pt -> pt.getName().equals(completionType)).findAny().get();
    }

    private AbstractProgramElement getAPE(Term term, SVInstantiations svInst) {
        assert term.sub(0).op() instanceof ProgramSV;
        final Object apeSVInst = svInst.getInstantiation((ProgramSV) term.sub(0).op());

        assert apeSVInst instanceof AbstractProgramElement;
        return (AbstractProgramElement) apeSVInst;
    }

}
