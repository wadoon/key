package de.uka.ilkd.key.util;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.NewVarcond;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.abstraction.Type;

public class LedgerDataTacletGenerator {

    private List<RewriteTaclet> newTaclets;
    Services services;
    private NamespaceSet nss;
    TermBuilder termBuilder;
    Function constructorFun, objectToLdFun, serFun, deserFun, readLdFun;
    Function lastEntryFun, getValueFun; // TODO where do we get these?
    Sort heapSort, intSort, objectSort, seqSort;
    Type intType, objectType;

    public LedgerDataTacletGenerator(Services services) {
        this.services = services;
        nss = services.getNamespaces();
        termBuilder = services.getTermBuilder();
        KeYJavaType intkjt = services.getJavaInfo().getKeYJavaType("int");
        intType = intkjt.getJavaType();
        intSort = intkjt.getSort();
        KeYJavaType objectkjt = services.getJavaInfo().getKeYJavaType("java.lang.Object");
        objectType = objectkjt.getJavaType();
        objectSort = objectkjt.getSort();
        heapSort = nss.sorts().lookup("Heap");
        seqSort = nss.sorts().lookup("Seq");
        newTaclets = new LinkedList<>();
    }

    public void createTaclets(LedgerData ld) {
        Sort ldSort = new SortImpl(new Name("k" + ld.getClass().getSimpleName()));
        KeYJavaType ldkjt = new KeYJavaType(new ClassDeclaration(), ldSort); // TODO how to build this?
        Field[] fields = getObjectFields(ld);
        ArrayList<SchemaVariable> schemaVars = new ArrayList<>();
        ArrayList<Function> getters = new ArrayList<>();
        ArrayList<Sort> sorts = new ArrayList<>();
        ArrayList<Type> types = new ArrayList<>();
        ArrayList<String> names = new ArrayList<>();
        ArrayList<KeYJavaType> kjts = new ArrayList<>();

        for (Field f : fields) {
            String fieldName = f.getName(); //TODO not sure this works
            String fieldTypeName = f.getType().getSimpleName();
            names.add(fieldName);
            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(fieldTypeName);
            kjts.add(kjt);
            Sort sort = kjt.getSort();
            sorts.add(sort);
            Type type = kjt.getJavaType();
            types.add(type);
            SchemaVariable sv = SchemaVariableFactory.createTermSV(new Name(fieldName), sort);
            schemaVars.add(sv);
            Function getFunc = new Function(new Name("get" + fieldName), sort, ldSort);
            getters.add(getFunc);
        }

        createFunctions(ld, ldSort, sorts);

        for (int i = 0; i < schemaVars.size(); ++i) {
            RewriteTaclet tac = createGetterTaclet(i, schemaVars, getters, types, ld, services);
            newTaclets.add(tac);
        }
        newTaclets.add(equalsTaclet(ldSort, ldkjt.getJavaType(), getters));
        newTaclets.add(objectToLdTaclet(fields, sorts, names, kjts, ldkjt));
        newTaclets.add(serializeTaclet(ldSort, ldkjt.getJavaType()));
        newTaclets.add(readLdTaclet());
    }

    public List<RewriteTaclet> getNewTaclets() {
        return newTaclets;
    }

    private RewriteTaclet readLdTaclet() {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        SchemaVariable indexVar = SchemaVariableFactory.createTermSV(new Name("index"), intSort);
        SchemaVariable seqVar = SchemaVariableFactory.createTermSV(new Name("sequence"), seqSort);
        tacletBuilder.addVarsNew(indexVar, intType);
        tacletBuilder.addVarsNew((NewVarcond) seqVar); //TODO
        Term iTerm = termBuilder.var(indexVar);
        Term seqTerm = termBuilder.var(seqVar);
        tacletBuilder.setFind(termBuilder.func(readLdFun, iTerm, seqTerm));
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        Term getValueTerm = termBuilder.func(getValueFun, termBuilder.func(lastEntryFun, iTerm, seqTerm));
        Term replaceWithTerm = termBuilder.func(deserFun, termBuilder.cast(seqSort, getValueTerm));
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));
        return tacletBuilder.getTaclet();
    }

    private RewriteTaclet serializeTaclet(Sort ldSort, Type ldType) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        SchemaVariable ldVar = SchemaVariableFactory.createTermSV(new Name("g"), ldSort);
        tacletBuilder.addVarsNew(ldVar, ldType);
        tacletBuilder.setFind(termBuilder.func(deserFun, termBuilder.func(serFun, termBuilder.var(ldVar))));
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(termBuilder.var(ldVar)));
        tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));
        return tacletBuilder.getTaclet();
    }

    private RewriteTaclet objectToLdTaclet(Field[] fields, ArrayList<Sort> sorts, ArrayList<String> names, ArrayList<KeYJavaType> types,
        KeYJavaType ldkjt) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        SchemaVariable objectVar = SchemaVariableFactory.createTermSV(new Name("o"), objectSort);
        SchemaVariable heapVar = SchemaVariableFactory.createTermSV(new Name("h"), heapSort);
        tacletBuilder.addVarsNew(objectVar, objectType);
        tacletBuilder.addVarsNew((NewVarcond) heapVar); //TODO
        Term heapVarTerm = termBuilder.var(heapVar);
        Term objectVarTerm = termBuilder.var(objectVar);
        Term findTerm = termBuilder.func(objectToLdFun, heapVarTerm, objectVarTerm);
        tacletBuilder.setFind(findTerm);
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        Term[] args = new Term[fields.length];
        for (int i = 0; i < fields.length; ++i) {
            ProgramElementName pen = new ProgramElementName(names.get(i));
            LocationVariable locVar = new LocationVariable(pen, types.get(i), ldkjt, false, false);
            args[i] = termBuilder.select(sorts.get(i), heapVarTerm, objectVarTerm, locVar);
        }

        Term replaceWithTerm = termBuilder.func(constructorFun, args);
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));

        tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));

        return tacletBuilder.getTaclet();
    }

    private RewriteTaclet equalsTaclet(Sort ldSort, Type ldType, ArrayList<Function> getters) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        SchemaVariable ldVar1 = SchemaVariableFactory.createTermSV(new Name("g"), ldSort);
        SchemaVariable ldVar2 = SchemaVariableFactory.createTermSV(new Name("g"), ldSort);
        tacletBuilder.addVarsNew(ldVar1, ldType);
        tacletBuilder.addVarsNew(ldVar2, ldType);
        tacletBuilder.setFind(termBuilder.equals(termBuilder.var(ldVar1), termBuilder.var(ldVar2)));
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        Term[] args = new Term[getters.size()];
        for (int i = 0; i < getters.size(); ++i) {
            Term getter1 = termBuilder.func(getters.get(i), termBuilder.var(ldVar1));
            Term getter2 = termBuilder.func(getters.get(i), termBuilder.var(ldVar2));
            args[i] = termBuilder.equals(getter1, getter2);
        }
        Term replaceWithTerm = termBuilder.and(args);
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));
        // tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));
        return tacletBuilder.getTaclet();
    }

    private void createFunctions(LedgerData ld, Sort keyld, ArrayList<Sort> argSorts) {
        String ldName = ld.getClass().getName();
        ImmutableArray<Sort> args = new ImmutableArray<>(argSorts);
        constructorFun = new Function(new Name("new" + ldName), keyld, args);
        objectToLdFun = new Function(new Name("object2" + ldName), heapSort, objectSort);
        serFun = new Function(new Name("serialize" + ldName), seqSort, keyld);
        deserFun = new Function(new Name("deserialize" + ldName), keyld, seqSort);
        readLdFun = new Function(new Name("read" + ldName), keyld, seqSort, intSort);
    }

    private RewriteTaclet createGetterTaclet(int i, List<SchemaVariable> schemaVars, List<Function> getters, List<Type> types, LedgerData ld,
        Services services) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        String fieldName = schemaVars.get(i).toString();
        Term[] varTerms = new Term[schemaVars.size()];
        for (int j = 0; j < schemaVars.size(); ++j) {
            varTerms[j] = termBuilder.var(schemaVars.get(j));
//            tacletBuilder.addVarsNew(schemaVars.get(j), types.get(j));
        }

        tacletBuilder.setName(new Name(fieldName + "OfNew" + ld.getClass().getName()));

        Term findTerm = termBuilder.func(getters.get(i), termBuilder.func(constructorFun, varTerms));
        tacletBuilder.setFind(findTerm);

        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);

        tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));

        Term replaceWithTerm = termBuilder.var(schemaVars.get(i));
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));

        return tacletBuilder.getTaclet();
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