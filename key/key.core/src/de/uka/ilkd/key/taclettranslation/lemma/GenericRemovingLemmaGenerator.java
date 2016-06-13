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

package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.HashMap;
import java.util.Map;

import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.SortDependingFunction;
import org.key_project.common.core.logic.sort.Sort;
import org.key_project.common.core.services.TermServices;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaDLTermServices;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProxySort;

/**
 * Generic removing lemma generator adds the default implementation only that all
 * {@link GenericSort}s are replaced to equally named {@link ProxySort}s.
 *
 * <p>This is done since the resulting term is to be used as a proof obligation
 * in which generic sorts must not appear; proxy sorts, however, may.
 *
 * For every generic sort, precisely one proxy sort is introduced.
 */
public class GenericRemovingLemmaGenerator extends DefaultLemmaGenerator {

    /**
     * The map from generic sorts to proxy sorts.
     */
    private final Map<Sort, Sort> sortMap = new HashMap<Sort, Sort>();


    /** {@inheritDoc}
     * <p>
     * The generic removing implementation replaces sort depending functions
     * if their sort argument is a generic sort.
     */
    @Override
    protected Operator replaceOp(Operator op, JavaDLTermServices services) {

        if (op instanceof SortDependingFunction) {
            SortDependingFunction sdf = (SortDependingFunction) op;
            Sort sort = sdf.getSortDependingOn();
            Sort repSort = replaceSort(sort, services);
            if(sort != repSort) {
                op = sdf.getInstanceFor(repSort, services);
            }
        }

        return op;
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * The generic removing implementation replaces generic sorts by equally
     * named proxy sorts.
     */
    @Override
    protected Sort replaceSort(Sort sort, JavaDLTermServices services) {
        if(sort instanceof GenericSort) {

            Sort cached = sortMap.get(sort);
            if(cached != null) {
                return cached;
            }

            ImmutableSet<Sort> extSorts = replaceSorts(sort.extendsSorts(), services);
            ProxySort result = new ProxySort(sort.name(), extSorts);
            sortMap.put(sort, result);
            return result;

        } else {
            return sort;
        }
    }

    /**
     * Replace sorts.
     *
     * @param extendsSorts
     *            the extends sorts
     * @param services
     *            the services
     * @return the immutable set
     */
    private ImmutableSet<Sort> replaceSorts(ImmutableSet<Sort> extendsSorts, JavaDLTermServices services) {
        ImmutableSet<Sort> result = DefaultImmutableSet.nil();
        for (Sort sort : extendsSorts) {
            result = result.add(replaceSort(sort, services));
        }
        return result;
    }
}