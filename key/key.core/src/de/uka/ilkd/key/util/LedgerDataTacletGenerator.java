package de.uka.ilkd.key.util;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.java.abstraction.Type;

public class LedgerDataTacletGenerator {

    private List<RewriteTaclet> newTaclets;
    private List<Function> newFunctions;
    Services services;
    TermBuilder termBuilder;

    public LedgerDataTacletGenerator(Services services) {
        this.services = services;
        newTaclets = new LinkedList<>();
        newFunctions = new LinkedList<>();
    }

    public void createTaclets(LedgerData ld) {
        Sort keyld = new SortImpl(new Name("k" + ld.getClass().getName()));
        Field[] fields = getObjectFields(ld);
        List<SchemaVariable> schemaVars = new LinkedList<>();
        for (Field f : fields) {
            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(f.getName());
            Type t = kjt.getJavaType();
            Sort sort = kjt.getSort();
            SchemaVariable sv = SchemaVariableFactory.createTermSV(new Name(f.getName()), sort);
            Function getFunc = new Function(new Name("get" + f.getName()), sort);
            newFunctions.add(getFunc);
            RewriteTaclet tac = createGetterTaclet(ld, f, fields, services);
            newTaclets.add(tac);
        }
    }

    private RewriteTaclet createGetterTaclet(LedgerData ld, Field f, Field[] fields, Services services) {
        RewriteTacletBuilder<RewriteTaclet> tb = new RewriteTacletBuilder<>();
        tb.setName(new Name(f.getName() + "OfNew" + ld.getClass().getName()));
        for (Field field : fields) {


            tb.addVarsNew(sv, t);
            schemaVars.add(sv);
        }
        findTerm = termBuilder.func(getFunc, termBuilder.func(newFunc));
        tb.setFind(findTerm);
        return tb.getTaclet();
    }

    public static Field[] getObjectFields(Object o) {
        Class<? extends Object> c = o.getClass();
        return c.getFields();
    }
}

/** superclass of all objects that can be stored on the ledger */
abstract class LedgerData {

    public abstract byte[] serialize(LedgerData ld);

    public abstract LedgerData deserialize(byte[] b);

}