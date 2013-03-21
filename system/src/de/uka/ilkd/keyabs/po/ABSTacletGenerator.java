package de.uka.ilkd.keyabs.po;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.logic.ABSTermBuilder;

/**
 * Created with IntelliJ IDEA.
 * User: bubel
 * Date: 20.03.13
 * Time: 17:18
 * To change this template use File | Settings | File Templates.
 */
public class ABSTacletGenerator {


    public Taclet generateTacletForInterfaceInvariant(KeYJavaType type, Term invAxiom, ABSServices services) {
        RewriteTacletBuilder rw = new RewriteTacletBuilder();

        Function func = services.getIInvFor(type);
        rw.setName(new Name("insertInvariantFor<" + type.getFullName() + ">"));
        rw.setFind(services.getTermBuilder().func(func));
        rw.addTacletGoalTemplate(new RewriteTacletGoalTemplate(invAxiom));

        return rw.getRewriteTaclet();
    }

    public Taclet generateTacletForClassInvariant(String className,
                                                  ImmutableSet<ClassInvariant> invAxioms,
                                                  ABSServices services) {
        RewriteTacletBuilder rw = new RewriteTacletBuilder();

        Function func = services.getCInv();
        rw.setName(new Name("insertClassInvariantFor<"+className+">"));

/*        SchemaVariable historySV = SchemaVariableFactory.createTermSV(new Name("historySV"),
                services.getTypeConverter().getHistoryLDT().targetSort());

        SchemaVariable heapSV = SchemaVariableFactory.createTermSV(new Name("heapSV"),
                services.getTypeConverter().getHeapLDT().targetSort());
  */
        SchemaVariable thisObjSV = SchemaVariableFactory.createTermSV(new Name("thisObjSV"),
                Sort.ANY);


        ABSTermBuilder TB = services.getTermBuilder();
        Term invAxiom = TB.tt();

        for (ClassInvariant inv : invAxioms) {
            invAxiom = ABSTermBuilder.TB.and(invAxiom, inv.getInv(thisObjSV, services));
        }

        rw.setFind(TB.func(func, TB.var(thisObjSV)));
        rw.addTacletGoalTemplate(new RewriteTacletGoalTemplate(invAxiom));


        return rw.getRewriteTaclet();
    }


}
