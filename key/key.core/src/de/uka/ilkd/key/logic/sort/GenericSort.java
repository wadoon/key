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

package de.uka.ilkd.key.logic.sort;

import java.util.Iterator;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.logic.sort.CCGenericSort;
import org.key_project.common.core.logic.sort.GenericSupersortException;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.util.collection.ImmutableSet;

/**
 * Sort used for generic taclets
 *
 * Within an SVInstantiations-object a generic sort is instantiated by a
 * concrete sort, which has to be a subsort of the instantiations of the
 * supersorts of this sort
 */
public final class GenericSort extends CCGenericSort {

    /**
     * A possible instantiation of this generic sort by a concrete sort must
     * satisfy each of these conditions:
     *
     * - if any generic supersort is to be instantiated simultanously, then this
     * instantiation has to be a supersort of the instantiation of this sort
     *
     * - the instantiation of this sort has to be a subsort of every concrete
     * supersort
     *
     * - if "oneOf" is not empty, the instantiation must be an element of
     * "oneOf"
     */

    /**
     * creates a generic sort
     * 
     * @param ext
     *            supersorts of this sort, which have to be either concrete
     *            sorts or plain generic sorts (i.e. not collection sorts of
     *            generic sorts)
     */
    public GenericSort(
            Name name,
            ImmutableSet<Sort> ext,
            ImmutableSet<Sort> oneOf)
            throws GenericSupersortException {
        super(name, ext, oneOf);
    }

    public GenericSort(Name name) {
        super(name);
    }

    @Override
    protected void checkSupersorts()
            throws GenericSupersortException {
        Iterator<Sort> it = extendsSorts().iterator();
        Sort s, t;
        while (it.hasNext()) {
            s = it.next();
            if (s instanceof ArraySort) {
                t = ((ArraySort) s).elementSort();
                while (t instanceof ArraySort)
                    t = ((ArraySort) t).elementSort();
                if (t instanceof GenericSort)
                    throw new GenericSupersortException("Illegal supersort "
                            + s +
                            " for generic sort " + name(),
                            s);
            }
        }
    }
}