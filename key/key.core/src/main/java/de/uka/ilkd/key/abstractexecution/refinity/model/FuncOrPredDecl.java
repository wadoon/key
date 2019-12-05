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
package de.uka.ilkd.key.abstractexecution.refinity.model;

import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * @author Dominic Steinhoefel
 */
public interface FuncOrPredDecl {
    String getName();

    boolean isFuncDecl();

    default boolean isPredDecl() {
        return !isFuncDecl();
    }

    List<String> getArgSorts();

    default FunctionDeclaration toFuncDecl() {
        assert isFuncDecl();
        return (FunctionDeclaration) this;
    }

    default PredicateDeclaration toPredDecl() {
        assert isPredDecl();
        return (PredicateDeclaration) this;
    }

    /**
     * Adds a function symbol corresponding to this {@link FuncOrPredDecl} to the
     * {@link Services} object if not already present.
     * 
     * @param services The {@link Services} object whose namespaces to populate.
     * @throws RuntimeException If the name is already present or some sort not
     *                          known.
     */
    default void checkAndRegister(final Services services) {
        final NamespaceSet namespaces = services.getNamespaces();

        final List<Sort> sorts = getArgSorts().stream().map(namespaces.sorts()::lookup)
                .collect(Collectors.toList());

        for (int i = 0; i < sorts.size(); i++) {
            if (sorts.get(i) == null) {
                throw new RuntimeException("The sort " + getArgSorts().get(i) + " is unknown.",
                        null);
            }
        }

        if (isPredDecl()) {
            final PredicateDeclaration predDecl = toPredDecl();

            if (namespaces.functions().lookup(predDecl.getPredName()) != null) {
                throw new RuntimeException("The predicate " + predDecl.getPredName()
                        + " is already registered, please choose another one.", null);
            }

            namespaces.functions().add(new Function(new Name(predDecl.getPredName()), Sort.FORMULA,
                    sorts.toArray(new Sort[0])));
        } else {
            final FunctionDeclaration funcDecl = toFuncDecl();

            if (namespaces.functions().lookup(funcDecl.getFuncName()) != null) {
                throw new RuntimeException("The function " + funcDecl.getFuncName()
                        + " is already registered, please choose another one.", null);
            }

            final Sort targetSort = namespaces.sorts().lookup(funcDecl.getResultSortName());
            if (targetSort == null) {
                throw new RuntimeException(
                        "The sort " + funcDecl.getResultSortName() + " is unknown.", null);
            }

            namespaces.functions().add(new Function(new Name(funcDecl.getFuncName()), targetSort,
                    sorts.toArray(new Sort[0])));
        }
    }

}
