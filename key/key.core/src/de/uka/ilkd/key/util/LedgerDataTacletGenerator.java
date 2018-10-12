package de.uka.ilkd.key.util;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class LedgerDataTacletGenerator {

    public static final RuleSet SIMPLIFY = new RuleSet(new Name("simplify"));
    private final Sort ldSort;
    Services services;
    private TermBuilder termBuilder;
    private Function constructorFun, objectToLdFun, serFun, deserFun, readLdFun;
    private Function lastEntryFun, getValueFun;
    private Sort heapSort, intSort, objectSort, seqSort;

    public LedgerDataTacletGenerator(Services services, KeYJavaType ldkjt) {
        this.services = services;
        this.ldSort = ldkjt.getSort();
        NamespaceSet nss = services.getNamespaces();
        termBuilder = services.getTermBuilder();
        KeYJavaType intkjt = services.getJavaInfo().getKeYJavaType("int");
        intSort = intkjt.getSort();
        KeYJavaType objectkjt = services.getJavaInfo().getKeYJavaType("java.lang.Object");
        objectSort = objectkjt.getSort();
        heapSort = nss.sorts().lookup("Heap");
        seqSort = nss.sorts().lookup("Seq");
        lastEntryFun = services.getNamespaces().functions().lookup("lastEntry");
        getValueFun = services.getNamespaces().functions().lookup("getValue");
    }

    public List<Taclet> createTaclets() {
        LinkedList<Taclet> res = new LinkedList<>();
        Collection<Sort> sorts = services.getNamespaces().sorts().allElements();
        Set<Sort> subSorts = childSorts(ldSort, sorts);

        for (Sort s : subSorts) {
            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(s);
            res.addAll(createTaclets(kjt));
        }

        return res;
    }

    List<Taclet> createTaclets(KeYJavaType ldkjt) {
        List<Taclet> newTaclets = new LinkedList<>();
        ImmutableList<Field> fields = services.getJavaInfo().getAllFields((TypeDeclaration) ldkjt.getJavaType());
        ArrayList<SchemaVariable> schemaVars = new ArrayList<>();
        ArrayList<Function> getters = new ArrayList<>();
        ArrayList<Sort> sorts = new ArrayList<>();
        ArrayList<String> names = new ArrayList<>();
        ArrayList<KeYJavaType> kjts = new ArrayList<>();

        for (Field f : fields) {
            String fieldName = f.getName();
            String fieldTypeName = f.getType().getName();
            names.add(fieldName);
            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(fieldTypeName);
            kjts.add(kjt);
            Sort sort = kjt.getSort();
            sorts.add(sort);
            SchemaVariable sv = SchemaVariableFactory.createTermSV(new Name(fieldName), sort);
            schemaVars.add(sv);
            Function getFunc = new Function(new Name("get" + fieldName), sort, ldSort);
            getters.add(getFunc);
        }

        createFunctions(ldkjt, ldSort, sorts);

        for (int i = 0; i < schemaVars.size(); ++i) {
            RewriteTaclet tac = createGetterTaclet(i, schemaVars, getters, ldkjt);
            newTaclets.add(tac);
        }
        newTaclets.add(equalsTaclet(ldSort, getters));
        newTaclets.add(objectToLdTaclet(fields, sorts, names, kjts, ldkjt));
        newTaclets.add(serializeTaclet(ldSort));
        newTaclets.add(readLdTaclet());

        return newTaclets;
    }

    private RewriteTaclet readLdTaclet() {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        SchemaVariable indexVar = SchemaVariableFactory.createTermSV(new Name("index"), intSort);
        SchemaVariable seqVar = SchemaVariableFactory.createTermSV(new Name("sequence"), seqSort);
        Term iTerm = termBuilder.var(indexVar);
        Term seqTerm = termBuilder.var(seqVar);
        tacletBuilder.setFind(termBuilder.func(readLdFun, iTerm, seqTerm));
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        Term getValueTerm = termBuilder.func(getValueFun, termBuilder.func(lastEntryFun, iTerm, seqTerm));
        Term replaceWithTerm = termBuilder.func(deserFun, termBuilder.cast(seqSort, getValueTerm));
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));
        return tacletBuilder.getTaclet();
    }

    private RewriteTaclet serializeTaclet(Sort ldSort) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        SchemaVariable ldVar = SchemaVariableFactory.createTermSV(new Name("g"), ldSort);
        tacletBuilder.setFind(termBuilder.func(deserFun, termBuilder.func(serFun, termBuilder.var(ldVar))));
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(termBuilder.var(ldVar)));
        tacletBuilder.addRuleSet(SIMPLIFY);
        return tacletBuilder.getTaclet();
    }

    private RewriteTaclet objectToLdTaclet(ImmutableList<Field> fields, ArrayList<Sort> sorts, ArrayList<String> names, ArrayList<KeYJavaType> types,
                                           KeYJavaType ldkjt) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        SchemaVariable objectVar = SchemaVariableFactory.createTermSV(new Name("o"), objectSort);
        SchemaVariable heapVar = SchemaVariableFactory.createTermSV(new Name("h"), heapSort);
        Term heapVarTerm = termBuilder.var(heapVar);
        Term objectVarTerm = termBuilder.var(objectVar);
        Term findTerm = termBuilder.func(objectToLdFun, heapVarTerm, objectVarTerm);
        tacletBuilder.setFind(findTerm);
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        Term[] args = new Term[fields.size()];
        for (int i = 0; i < fields.size(); ++i) {
            ProgramElementName pen = new ProgramElementName(names.get(i));
            LocationVariable locVar = new LocationVariable(pen, types.get(i), ldkjt, false, false);
            args[i] = termBuilder.select(sorts.get(i), heapVarTerm, objectVarTerm, locVar);
        }

        Term replaceWithTerm = termBuilder.func(constructorFun, args);
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));

        tacletBuilder.addRuleSet(SIMPLIFY);

        return tacletBuilder.getTaclet();
    }

    private RewriteTaclet equalsTaclet(Sort ldSort, ArrayList<Function> getters) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        SchemaVariable ldVar1 = SchemaVariableFactory.createTermSV(new Name("g"), ldSort);
        SchemaVariable ldVar2 = SchemaVariableFactory.createTermSV(new Name("g"), ldSort);
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
        return tacletBuilder.getTaclet();
    }

    private void createFunctions(KeYJavaType kjt, Sort keyld, ArrayList<Sort> argSorts) {
        String ldName = kjt.getName();
        ImmutableArray<Sort> args = new ImmutableArray<>(argSorts);
        constructorFun = new Function(new Name("new" + ldName), keyld, args);
        objectToLdFun = new Function(new Name("object2" + ldName), heapSort, objectSort);
        serFun = new Function(new Name("serialize" + ldName), seqSort, keyld);
        deserFun = new Function(new Name("deserialize" + ldName), keyld, seqSort);
        readLdFun = new Function(new Name("read" + ldName), keyld, seqSort, intSort);
    }

    private RewriteTaclet createGetterTaclet(int i, List<SchemaVariable> schemaVars,
                                             List<Function> getters, KeYJavaType ldkjt) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        String fieldName = schemaVars.get(i).toString();
        Term[] varTerms = new Term[schemaVars.size()];
        for (int j = 0; j < schemaVars.size(); ++j) {
            varTerms[j] = termBuilder.var(schemaVars.get(j));
        }

        tacletBuilder.setName(new Name(fieldName + "OfNew" + ldkjt.getName()));

        Term findTerm = termBuilder.func(getters.get(i), termBuilder.func(constructorFun, varTerms));
        tacletBuilder.setFind(findTerm);

        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);

        tacletBuilder.addRuleSet(SIMPLIFY);

        Term replaceWithTerm = termBuilder.var(schemaVars.get(i));
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));

        return tacletBuilder.getTaclet();
    }

    private Set<Sort> childSorts(Sort s, Collection<Sort> sorts) {
        Set<Sort> res = new HashSet<>();
        for (Sort child : sorts) {
            if (!(s instanceof NullSort) && s.extendsTrans(child)) {
                res.add(child);
            }
        }
        return res;
    }
}