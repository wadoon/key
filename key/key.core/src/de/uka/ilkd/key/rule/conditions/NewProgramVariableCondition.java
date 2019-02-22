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

package de.uka.ilkd.key.rule.conditions;

import java.util.Optional;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Instantiates a {@link ProgramSV} with a fresh variable of the given type.
 *
 * @author Dominic Steinhöfel
 */
public class NewProgramVariableCondition implements VariableCondition {
    private final ProgramSV newSV;
    private final String namePattern;
    private final Optional<KeYJavaType> type;
    private final Optional<ProgramSV> maybePeerSV;
    private final Optional<SchemaVariable> maybeFreshForSV;

    public NewProgramVariableCondition(ProgramSV newSV, String namePattern,
            KeYJavaType type, ProgramSV freshForSV) {
        this.newSV = newSV;
        this.namePattern = namePattern;
        this.type = Optional.of(type);
        this.maybeFreshForSV = Optional.ofNullable(freshForSV);
        this.maybePeerSV = Optional.empty();
    }

    public NewProgramVariableCondition(ProgramSV newSV, String namePattern,
            ProgramSV peerSV, ProgramSV freshForSV) {
        this.newSV = newSV;
        this.namePattern = namePattern;
        this.maybePeerSV = Optional.of(peerSV);
        this.maybeFreshForSV = Optional.ofNullable(freshForSV);
        this.type = Optional.empty();
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.isInstantiated(newSV)) {
            return matchCond;
        }

        final Optional<MatchConditions> maybeStoredResult =
                maybeFreshForSV.flatMap(freshForSV -> Optional
                        .ofNullable(svInst.getInstantiation(freshForSV))
                        .flatMap(inst -> services
                                .getFreshForInstantiation(inst, newSV)
                                .map(LocationVariable.class::cast)
                                .map(freshForInst -> matchCond
                                        .setInstantiations(svInst.add(newSV,
                                                freshForInst, services)))));

        if (maybeStoredResult.isPresent()) {
            return maybeStoredResult.get();
        }

        final KeYJavaType type = this.type.orElseGet(() -> maybePeerSV
                .map(svInst::getInstantiation).map(ProgramVariable.class::cast)
                .map(ProgramVariable::getKeYJavaType).orElseThrow());

        final String newName = services.getTermBuilder().newName(namePattern);
        final LocationVariable result =
                new LocationVariable(new ProgramElementName(newName), type);
        services.getNamespaces().programVariables().add(result);

        maybeFreshForSV
                .ifPresent(freshForSV -> services.addFreshForInstantiation(
                        svInst.getInstantiation(freshForSV), newSV, result));

        return matchCond.setInstantiations(svInst.add(newSV, result, services));
    }

    @Override
    public String toString() {
        return String.format("\\varcond(\\newPV(%s, \"%s\", %s%s))", newSV,
                namePattern,
                maybePeerSV.map(psv -> "\\typeof(" + psv + ")")
                        .orElse(type.map(KeYJavaType::getSort)
                                .map(Sort::toString).orElse("ERROR")),
                maybeFreshForSV.map(sv -> " \\freshFor(" + sv + ")")
                        .orElse(""));
    }
}
