// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package org.key_project.common.core.ldt;

import org.key_project.common.core.logic.CCTerm;
import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.Named;
import org.key_project.common.core.logic.Namespace;
import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.SortDependingFunction;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.program.abstraction.CCType;
import org.key_project.common.core.services.TermServices;

/**
 * An "LDT" or "language data type" class corresponds to a standard rule file
 * shipped with KeY. Usually, this rule file declares a sort (such as "int") and
 * a number of operators. The LDT class provides a programming interface to
 * access these entities, and it assists the type converter in handling them.
 */
public abstract class CC_LDT<T extends CCTerm<?, ?, ?>> implements Named {

    private final Name name;

    /** the main sort associated with the LDT */
    private final Sort sort;

    /** the namespace of functions this LDT feels responsible for */
    private final Namespace functions = new Namespace();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    protected CC_LDT(Name name, TermServices services) {
        sort = (Sort) services.getNamespaces().sorts().lookup(name);
        if (sort == null)
            throw new RuntimeException(
                    "LDT "
                            + name
                            + " not found.\n"
                            +
                            "It seems that there are definitions missing from the .key files.");
        this.name = name;
    }

    protected CC_LDT(Name name, Sort targetSort) {
        sort = targetSort;
        if (sort == null)
            throw new RuntimeException(
                    "LDT "
                            + name
                            + " not found.\n"
                            +
                            "It seems that there are definitions missing from the .key files.");
        this.name = name;
    }

    // -------------------------------------------------------------------------
    // protected methods
    // -------------------------------------------------------------------------

    /**
     * adds a function to the LDT
     * 
     * @return the added function (for convenience reasons)
     */
    protected final Function addFunction(Function f) {
        functions.addSafely(f);
        return f;
    }

    /**
     * looks up a function in the namespace and adds it to the LDT
     * 
     * @param funcName
     *            the String with the name of the function to look up
     * @return the added function (for convenience reasons)
     */
    protected final Function addFunction(TermServices services,
            String funcName) {
        final Namespace funcNS = services.getNamespaces().functions();
        final Function f = (Function) funcNS.lookup(new Name(funcName));
        if (f == null)
            throw new RuntimeException(
                    "LDT: Function "
                            + funcName
                            + " not found.\n"
                            +
                            "It seems that there are definitions missing from the .key files.");
        return addFunction(f);
    }

    protected final SortDependingFunction addSortDependingFunction(
            TermServices services,
            String kind) {
        final SortDependingFunction f =
                services.getFirstInstance(new Name(kind));
        assert f != null : "LDT: Sort depending function "
                + kind + " not found";
        addFunction(f);
        return f;
    }

    /**
     * returns the basic functions of the model
     * 
     * @return the basic functions of the model
     */
    protected final Namespace functions() {
        return functions;
    }

    // -------------------------------------------------------------------------
    // public methods
    // -------------------------------------------------------------------------

    @Override
    public final Name name() {
        return name;
    }

    @Override
    public final String toString() {
        return "LDT " + name() + " (" + targetSort() + ")";
    }

    /**
     * Returns the sort associated with the LDT.
     */
    public final Sort targetSort() {
        return sort;
    }

    public boolean containsFunction(Function op) {
        Named n = functions.lookup(op.name());
        return (n == op);
    }

    // -------------------------------------------------------------------------
    // abstract methods
    // -------------------------------------------------------------------------

    public abstract boolean hasLiteralFunction(Function f);

    public abstract CCType getType(T t);
}
