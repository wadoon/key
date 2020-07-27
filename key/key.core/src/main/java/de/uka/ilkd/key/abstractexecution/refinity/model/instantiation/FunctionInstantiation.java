// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.abstractexecution.refinity.model.instantiation;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

import de.uka.ilkd.key.abstractexecution.refinity.model.FuncOrPredDecl;
import de.uka.ilkd.key.abstractexecution.refinity.model.FunctionDeclaration;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * @author Dominic Steinhoefel
 */
@XmlRootElement
@XmlAccessorType(XmlAccessType.FIELD)
public class FunctionInstantiation {
    @XmlElement(name = "declaration")
    private FunctionDeclaration declaration;
    @XmlElement(name = "instantiation")
    private String instantiation;
    @XmlElement(name = "resultSort")
    private String resultSort;
    @XmlElement(name = "instArgSort")
    private List<String> instArgSorts = new ArrayList<>();

    public FunctionInstantiation() {
    }

    public FunctionInstantiation(final FunctionDeclaration declaration, final String instantiation,
            final String resultSort, final List<String> instArgSorts) {
        this.declaration = declaration;
        this.instantiation = instantiation;
        this.resultSort = resultSort;
        this.instArgSorts = instArgSorts;
    }

    public FunctionDeclaration getDeclaration() {
        return declaration;
    }

    public void setDeclaration(FunctionDeclaration declaration) {
        this.declaration = declaration;
    }

    public String getInstantiation() {
        return instantiation;
    }

    public void setInstantiation(String instantiation) {
        this.instantiation = instantiation;
    }

    public String getResultSort() {
        return resultSort;
    }

    public void setResultSort(String resultSort) {
        this.resultSort = resultSort;
    }

    public List<String> getInstArgSorts() {
        return instArgSorts;
    }

    public void setInstArgSorts(List<String> instArgSorts) {
        this.instArgSorts = instArgSorts;
    }

    /**
     * Adds a function symbol corresponding to this {@link FuncOrPredDecl} to the
     * {@link Services} object if not already present.
     * 
     * @param services The {@link Services} object whose namespaces to populate.
     * @throws RuntimeException If the name is already present or some sort not
     * known.
     */
    public void checkAndRegister(final Services services) {
        assert declaration != null;
        assert instantiation != null;
        assert instArgSorts != null;
        assert resultSort != null;
        
        final NamespaceSet namespaces = services.getNamespaces();

        final List<Sort> sorts = //
                getInstArgSorts().stream().map(namespaces.sorts()::lookup)
                        .collect(Collectors.toList());

        for (int i = 0; i < sorts.size(); i++) {
            if (sorts.get(i) == null) {
                throw new RuntimeException("The sort " + getInstArgSorts().get(i) + " is unknown.",
                        null);
            }
        }

        final String funcName = declaration.getFuncName();

        if (namespaces.functions().lookup(funcName) != null) {
            throw new RuntimeException("The function " + funcName
                    + " is already registered, please choose another one.", null);
        }

        final Sort targetSort = namespaces.sorts().lookup(resultSort);
        if (targetSort == null) {
            throw new RuntimeException("The sort " + resultSort + " is unknown.", null);
        }

        namespaces.functions()
                .add(new Function(new Name(funcName), targetSort, sorts.toArray(new Sort[0])));
    }

    public String toDeclarationString() {
        if (instArgSorts.isEmpty()) {
            return String.format("%s %s;", resultSort, declaration.getFuncName());
        }

        return String.format("%s %s(%s);", resultSort, declaration.getFuncName(),
                instArgSorts.stream().collect(Collectors.joining(", ")));
    }

    @Override
    public String toString() {
        assert declaration != null;
        assert instantiation != null;
        assert instArgSorts != null;
        assert resultSort != null;

        Supplier<IntStream> stream = () -> IntStream.range(1, instArgSorts.size() + 1);

        final String qfdParamDecl = stream.get()
                .mapToObj(i -> String.format("(\\forall %s _p%d; ", instArgSorts.get(i - 1), i))
                .collect(Collectors.joining());

        final String paramList = stream.get().mapToObj(i -> String.format("_p%d", i))
                .collect(Collectors.joining(", "));

        final String closingParens = stream.get().mapToObj(i -> ")").collect(Collectors.joining());

        return qfdParamDecl
                + String.format("(%s%s = %s)", declaration.getFuncName(),
                        instArgSorts.size() == 0 ? "" : "(" + paramList + ")", instantiation)
                + closingParens;
    }

    @Override
    public boolean equals(Object obj) {
        return obj != null && (obj instanceof FunctionInstantiation)
                && ((FunctionInstantiation) obj).declaration.equals(this.declaration)
                && ((FunctionInstantiation) obj).instantiation.equals(this.instantiation)
                && ((FunctionInstantiation) obj).resultSort.equals(this.resultSort)
                && ((FunctionInstantiation) obj).instArgSorts.equals(this.instArgSorts);
    }

}
