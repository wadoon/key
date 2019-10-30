// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.abstractexecution.rule.conditions;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import de.uka.ilkd.key.abstractexecution.java.statement.AbstractPlaceholderStatement;
import de.uka.ilkd.key.abstractexecution.util.AbstractExecutionContractUtils;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Instantiates a parametric skolem path condition for abstract execution. The
 * such generated formula receives one LocSet for its assignable; those are
 * obtained from the block contracts of the {@link AbstractPlaceholderStatement}
 * it is generated for.
 *
 * @author Dominic Steinhoefel
 */
public class InitializeParametricSkolemPathCondition implements VariableCondition {
    private final SchemaVariable pathCondSV;
    private final ProgramSV abstrProgSV;

    public InitializeParametricSkolemPathCondition(SchemaVariable pathCondSV,
            ProgramSV abstrProgSV) {
        this.pathCondSV = pathCondSV;
        this.abstrProgSV = abstrProgSV;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();
        final TermBuilder tb = services.getTermBuilder();

        final Optional<ExecutionContext> executionContext = Optional
                .ofNullable(svInst.getExecutionContext());

        if (svInst.isInstantiated(pathCondSV)) {
            return matchCond;
        }

        final AbstractPlaceholderStatement abstrStmt = //
                (AbstractPlaceholderStatement) svInst.getInstantiation(abstrProgSV);

        final List<Term> accessibles = AbstractExecutionContractUtils
                .getAccessibleAndAssignableTermsForNoBehaviorContract(abstrStmt, matchCond,
                        services, executionContext).first.stream().map(loc -> loc.toTerm(services))
                                .map(tb::value).collect(Collectors.toList());
        final Sort[] accessiblesSorts = accessibles.stream().map(Term::sort)
                .collect(Collectors.toList()).toArray(new Sort[0]);

        final Function funcSymb = services.abstractUpdateFactory()
                .getAbstractPathConditionInstance(abstrStmt, accessiblesSorts);

        final Term pathCond = tb.func(funcSymb, accessibles.toArray(new Term[0]));

        return matchCond.setInstantiations(svInst.add(pathCondSV, pathCond, services));
    }

    @Override
    public String toString() {
        final List<SchemaVariable> svs = new ArrayList<>();
        svs.add(pathCondSV);
        svs.add(abstrProgSV);

        final String svsString = svs.stream().map(SchemaVariable::toString)
                .collect(Collectors.joining(", "));

        return String.format("\\varcond (\\initializeParametricSkolemPathCondition(%s))",
                svsString);
    }
}
