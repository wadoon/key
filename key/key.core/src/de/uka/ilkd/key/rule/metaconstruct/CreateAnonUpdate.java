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

package de.uka.ilkd.key.rule.metaconstruct;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.MiscTools;

public final class CreateAnonUpdate extends AbstractTermTransformer {

    public CreateAnonUpdate() {
        super(new Name("#createAnonUpdate"), 1);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst,
            Services services) {
        final Term target = term.sub(0);

        // the target term should have a Java block
        final ProgramElement pe = target.javaBlock().program();
        assert pe != null;

        final ImmutableSet<ProgramVariable> localOuts = MiscTools
                .getLocalOuts(pe, services);
        return createLocalAnonUpdate(localOuts, services);
    }

    private static Term createLocalAnonUpdate(
            ImmutableSet<ProgramVariable> localOuts, Services services) {
        final TermBuilder tb = services.getTermBuilder();

        Term anonUpdate = tb.skip();
        for (ProgramVariable pv : localOuts) {
            Function anonFunc = anonConstForPV(pv, services);
            final Term elemUpd = //
                    tb.elementary((LocationVariable) pv, tb.func(anonFunc));
            anonUpdate = tb.parallel(anonUpdate, elemUpd);
        }

        return anonUpdate;
    }

    private static Function anonConstForPV(ProgramVariable pv,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
        final Function anonFunc = new Function(anonFuncName, pv.sort(), true);
        services.getNamespaces().functions().addSafely(anonFunc);

        return anonFunc;
    }
}