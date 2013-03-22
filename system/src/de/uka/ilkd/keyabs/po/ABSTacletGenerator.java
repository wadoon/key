package de.uka.ilkd.keyabs.po;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.abs.abstraction.ABSInterfaceType;
import de.uka.ilkd.keyabs.logic.ABSTermBuilder;
import de.uka.ilkd.keyabs.speclang.dl.ABSClassInvariant;
import de.uka.ilkd.keyabs.speclang.dl.InterfaceInvariant;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 20.03.13
 * Time: 17:18
 * To change this template use File | Settings | File Templates.
 */
public class ABSTacletGenerator {


    public Taclet generateTacletForInterfaceInvariant(KeYJavaType type,
                                                      ImmutableSet<InterfaceInvariant> invs,
                                                      ABSServices services) {
        RewriteTacletBuilder rw = new RewriteTacletBuilder();

        Function func = services.getIInvFor(type);

        SchemaVariable historySV = SchemaVariableFactory.createTermSV(new Name("historySV"),
                services.getTypeConverter().getHistoryLDT().targetSort());

        Term invAxiom = ABSTermBuilder.TB.tt();

        for (InterfaceInvariant inv : invs) {
            invAxiom = ABSTermBuilder.TB.and(invAxiom, inv.getInvariant(historySV));
        }


        rw.setName(new Name("insertInvariantFor<" + type.getFullName() + ">"));
        rw.setFind(services.getTermBuilder().func(func, services.getTermBuilder().var(historySV)));


        rw.addTacletGoalTemplate(new RewriteTacletGoalTemplate(invAxiom));

        return rw.getRewriteTaclet();
    }

    public Taclet generateTacletForClassInvariant(String className,
                                                  ImmutableSet<ABSClassInvariant> invAxioms,
                                                  ABSServices services) {
        RewriteTacletBuilder rw = new RewriteTacletBuilder();

        Function func = services.getCInv();
        rw.setName(new Name("insertClassInvariantFor<"+className+">"));

        SchemaVariable historySV = SchemaVariableFactory.createTermSV(new Name("historySV"),
                services.getTypeConverter().getHistoryLDT().targetSort());

        SchemaVariable heapSV = SchemaVariableFactory.createTermSV(new Name("heapSV"),
                services.getTypeConverter().getHeapLDT().targetSort());

        SchemaVariable thisObjSV = SchemaVariableFactory.createTermSV(new Name("thisObjSV"),
                Sort.ANY);


        ABSTermBuilder TB = services.getTermBuilder();
        Term invAxiom = TB.tt();

        for (ABSClassInvariant inv : invAxioms) {
            invAxiom = ABSTermBuilder.TB.and(invAxiom, inv.getInv(historySV, heapSV, thisObjSV, services));
        }

        rw.setFind(TB.func(func, TB.var(historySV), TB.var(heapSV), TB.var(thisObjSV)));
        rw.addTacletGoalTemplate(new RewriteTacletGoalTemplate(invAxiom));

        return rw.getRewriteTaclet();
    }


}
