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

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.ProgramList;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Instantiate a list {@link ProgramSV} with fresh variables of the given type.
 * The length of the list is either taken from the length of another list of
 * schema variables or a numeric constant. The base name for the new variables
 * can be set via a parameter.
 *
 * @author Dominic Steinhoefel
 */
public class InstantiateVarsFreshCondition implements VariableCondition {
    private final ProgramSV varsList;
    private final ProgramSV varsListForLength;
    private final int size;
    private final String namePattern;
    private final KeYJavaType type;
    private final Optional<SchemaVariable> freshForSV;

    public InstantiateVarsFreshCondition(ProgramSV varsList,
            ProgramSV varsListForLength, String namePattern, KeYJavaType type,
            SchemaVariable freshForSV) {
        assert varsList.isListSV();
        assert varsListForLength.isListSV();

        this.varsList = varsList;
        this.varsListForLength = varsListForLength;
        this.size = -1;
        this.namePattern = namePattern;
        this.type = type;
        this.freshForSV = Optional.ofNullable(freshForSV);
    }

    public InstantiateVarsFreshCondition(ProgramSV varsList, int size,
            String namePattern, KeYJavaType type, SchemaVariable freshForSV) {
        assert varsList.isListSV();

        this.varsList = varsList;
        this.varsListForLength = null;
        this.size = size;
        this.namePattern = namePattern;
        this.type = type;
        this.freshForSV = Optional.ofNullable(freshForSV);
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.isInstantiated(varsList)) {
            return matchCond;
        }

        if (freshForSV.isPresent() && svInst.isInstantiated(freshForSV.get())
                && services.getFreshForInstantiation(
                        svInst.getInstantiation(freshForSV.get()), varsList)
                        .isPresent()) {
            return matchCond.setInstantiations(svInst.add(varsList,
                    (ProgramList) services.getFreshForInstantiation(
                            svInst.getInstantiation(freshForSV.get()), varsList)
                            .get(),
                    services));
        }

        @SuppressWarnings("rawtypes")
        final IProgramVariable[] freshVars = //
                new IProgramVariable[varsListForLength == null ? size
                        : ((ImmutableArray) svInst
                                .getInstantiation(varsListForLength)).size()];

        for (int i = 0; i < freshVars.length; i++) {
            final String newName =
                    services.getTermBuilder().newName(namePattern);
            freshVars[i] = //
                    new LocationVariable(new ProgramElementName(newName), type);
            services.getNamespaces().programVariables().add(freshVars[i]);
        }

        ProgramList pl =
                new ProgramList(new ImmutableArray<ProgramElement>(freshVars));

        if (freshForSV.isPresent()) {
            services.addFreshForInstantiation(
                    svInst.getInstantiation(freshForSV.get()), varsList, pl);
        }

        return matchCond.setInstantiations(svInst.add(varsList, pl, services));
    }

    @Override
    public String toString() {
        return String.format(
                "\\varcond (\\instantiateVarsFresh(%s, %s, \"%s\", %s%s)",
                varsList,
                Optional.ofNullable(varsListForLength).map(ProgramSV::toString)
                        .orElse("" + size),
                namePattern, type.getSort(),
                freshForSV.map(sv -> " \\freshFor(" + sv + ")").orElse(""));
    }
}
