package de.uka.ilkd.keyabs.proof.init;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.logic.ABSTermBuilder;
import de.uka.ilkd.keyabs.speclang.dl.ABSClassInvariant;
import de.uka.ilkd.keyabs.speclang.dl.InterfaceInvariant;

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
            invAxiom = ABSTermBuilder.TB.and(invAxiom, inv.getInvariant(historySV, services));
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
                services.getProgramInfo().getAnyInterfaceSort());


        ABSTermBuilder TB = services.getTermBuilder();
        Term invAxiom = TB.tt();

        for (ABSClassInvariant inv : invAxioms) {
            System.out.println(inv.getOriginalInv());
            System.out.println(inv.getInv(historySV, heapSV, thisObjSV, services));
            invAxiom = ABSTermBuilder.TB.and(invAxiom, inv.getInv(historySV, heapSV, thisObjSV, services));
        }

        rw.setFind(TB.func(func, TB.var(historySV), TB.var(heapSV), TB.var(thisObjSV)));
        rw.addTacletGoalTemplate(new RewriteTacletGoalTemplate(invAxiom));

        rw.addRuleSet(new RuleSet(new Name("partialInvAxiom")));
        return rw.getRewriteTaclet();
    }


}
