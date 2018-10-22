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

    /** Ruleset for Taclets that should be always be used by automation */
    public static final RuleSet SIMPLIFY = new RuleSet(new Name("simplify"));
    /** The sort of the LedgerData type, which is extended by the initially unknown actual Ledger Types. */
    private final Sort superSort;
    /** Services. Everyone needs them */
    Services services;
    /** DL functions that already exist */
    private Function lastEntryFun, getValueFun, a2sFun;
    /** Some KeY sorts that are needed for generation */
    private Sort heapSort, intSort, objectSort, seqSort;
    /** The new DL functions that are needed in the proof */
    private ArrayList<Function> newFunctions;
    /** DL Functions for the supertype that will be generated in the constructor */
    private Function superObjectToLdFun, superSerFun, superDeserFun;
    /** A Termbuilder needed for the Taclet generation */
    private TermBuilder termBuilder;

    /**
     *  Constructor. Already existing sorts and functions are looked up; and some supertype functions are created here.
     * @param services Services. Everyone needs them
     * @param ldkjt The {@link KeYJavaType} of the LedgerData supertype
     */
    public LedgerDataTacletGenerator(Services services, KeYJavaType ldkjt) {
        this.services = services;
        this.superSort = ldkjt.getSort();
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
        a2sFun = services.getNamespaces().functions().lookup("array2seq");
        newFunctions = new ArrayList<>();
        String ldName = ldkjt.getName();
        superObjectToLdFun = new Function(new Name("object2" + ldName), superSort,  heapSort, objectSort);
        superSerFun = new Function(new Name("serialize" + ldName), seqSort, superSort);
        superDeserFun = new Function(new Name("deserialize" + ldName), superSort, seqSort);
        newFunctions.add(superDeserFun);
        newFunctions.add(superSerFun);
        newFunctions.add(superObjectToLdFun);
    }

    /**
     * Toplevel Taclet generation. Creates taclets that are needed for reasoning about reading from / writing to
     * a ledger, for every subsort of the LedgerData type.
     * @return A list of Taclets that can be added to a proof config to enable ledger reasoning.
     */
    public List<Taclet> createTaclets() {
        LinkedList<Taclet> res = new LinkedList<>();
        Collection<Sort> sorts = services.getNamespaces().sorts().allElements();
        Set<Sort> subSorts = childSorts(superSort, sorts);

        for (Sort s : subSorts) {
            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(s);
            res.addAll(createTaclets(kjt));
        }

        return res;
    }

    /**
     * Taclet generation for a specific type.
     * @param dataKJT The {@link KeYJavaType} of the specific LedgerData subtype.
     * @return All the Taclets for the specific type.
     */
    private List<Taclet> createTaclets(KeYJavaType dataKJT) {
        List<Taclet> newTaclets = new LinkedList<>();
        ImmutableList<Field> allFields = services.getJavaInfo().getAllFields((TypeDeclaration) dataKJT.getJavaType());
        ArrayList<Field> fields = new ArrayList<>();
        for (Field f : allFields) {
            if (!(f.getFullName().contains("class"))) { //TODO horrible hack to exclude implicit fields. how to only get ACTUAL fields?
                fields.add(f);
            }
        }
        ArrayList<SchemaVariable> schemaVars = new ArrayList<>();
        ArrayList<Function> getters = new ArrayList<>();
        ArrayList<Sort> sorts = new ArrayList<>();
        ArrayList<String> names = new ArrayList<>();
        ArrayList<String> shortFieldNames = new ArrayList<>();
        ArrayList<KeYJavaType> kjts = new ArrayList<>();

        for (Field f : fields) {
            String fieldName = f.toString();
            String s1 = fieldName.split("::")[0];
            String s2 = fieldName.split("::")[1];
            String ucs2 = s2.substring(0, 1).toUpperCase() + s2.substring(1);
            String prettyFieldName = s1 + ucs2;
            String fieldTypeName = f.getType().getName();
            names.add(fieldName);
            shortFieldNames.add(s2);
            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(fieldTypeName);
            kjts.add(kjt);
            Sort sort = kjt.getSort();
            sorts.add(sort);
            SchemaVariable sv = SchemaVariableFactory.createTermSV(new Name(prettyFieldName), sort);
            schemaVars.add(sv);
            Function getFunc = new Function(new Name("get" + prettyFieldName), sort, superSort);
            getters.add(getFunc);
        }

        String ldName = dataKJT.getName();
        Sort ldSort = dataKJT.getSort();
        Function constructorFun, objectToLdFun, serFun, deserFun, readLdFun;
        constructorFun = new Function(new Name("new" + ldName), ldSort, new ImmutableArray<>(sorts));
        objectToLdFun = new Function(new Name("object2" + ldName), ldSort,  heapSort, objectSort);
        serFun = new Function(new Name("serialize" + ldName), seqSort, ldSort);
        deserFun = new Function(new Name("deserialize" + ldName), ldSort, seqSort);
        readLdFun = new Function(new Name("read" + ldName), ldSort, seqSort, intSort);
        newFunctions.add(constructorFun);
        newFunctions.add(objectToLdFun);
        newFunctions.add(serFun);
        newFunctions.add(deserFun);
        newFunctions.add(readLdFun);

        newFunctions.addAll(getters);

        for (int i = 0; i < schemaVars.size(); ++i) {
            RewriteTaclet tac = createGetterTaclet(i, schemaVars, getters, dataKJT, shortFieldNames.get(i), constructorFun);
            newTaclets.add(tac);
        }
        newTaclets.add(equalsTaclet(dataKJT.getSort(), getters));
        newTaclets.add(objectToLdTaclet(fields, sorts, names, kjts, dataKJT, objectToLdFun, constructorFun));
        newTaclets.add(serializeTaclet(dataKJT.getSort(), deserFun, serFun));
        newTaclets.add(readLdTaclet(dataKJT, readLdFun, deserFun));
        newTaclets.add(serializationExtensionTaclet(dataKJT, serFun, objectToLdFun));
        newTaclets.add(deserializationExtensionTaclet(dataKJT, deserFun, objectToLdFun));

        return newTaclets;
    }

    /**
     * Generates a taclet that expresses that reading from a ledger yields an object equal to
     * the deserialization of the byte array in the ledger at the given position.
     * @param kjt the {@link KeYJavaType} for which the taclet is generated
     * @param readLdFun The "read" KeY Function
     * @param deserFun The "deserialize" KeY Function
     * @return The read taclet
     */
    private RewriteTaclet readLdTaclet(KeYJavaType kjt, Function readLdFun, Function deserFun) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setName(new Name("read" + kjt.getName()));
        SchemaVariable indexVar = SchemaVariableFactory.createTermSV(new Name("index"), intSort);
        SchemaVariable seqVar = SchemaVariableFactory.createTermSV(new Name("sequence"), seqSort);
        Term iTerm = termBuilder.var(indexVar);
        Term seqTerm = termBuilder.var(seqVar);
        tacletBuilder.setFind(termBuilder.func(readLdFun, seqTerm, iTerm));
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        Term getValueTerm = termBuilder.func(getValueFun, termBuilder.func(lastEntryFun, seqTerm, iTerm));
        Term replaceWithTerm = termBuilder.func(deserFun, termBuilder.cast(seqSort, getValueTerm));
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));
        return tacletBuilder.getTaclet();
    }

    /**
     * Generates a taclet which expresses that serialization followed by deserialization
     * of an object yields the same object.
     * @param ldSort the sort for which the taclet is generated
     * @param deserFun the deserialization function
     * @param serFun the serialization function
     * @return the serialize taclet
     */
    private RewriteTaclet serializeTaclet(Sort ldSort, Function deserFun, Function serFun) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setName(new Name("serialize" + ldSort.name()));
        SchemaVariable ldVar = SchemaVariableFactory.createTermSV(new Name("ld"), ldSort);
        tacletBuilder.setFind(termBuilder.func(deserFun, termBuilder.func(serFun, termBuilder.var(ldVar))));
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(termBuilder.var(ldVar)));
        tacletBuilder.addRuleSet(SIMPLIFY);
        return tacletBuilder.getTaclet();
    }

    /**
     * Generates a taclet that enables "casting" from an unknown java object to the given ledger data type.
     * @param fields the fields of the data type
     * @param sorts the KeY sorts of the fields
     * @param names the names of the fields
     * @param types the types of the fields
     * @param ldkjt the {@link KeYJavaType} for which the taclet is generated
     * @param objectToLdFun the Object-to-ledgerdata function for this type
     * @param constructorFun the constructor function for this type
     * @return the object2ld taclet
     */
    private RewriteTaclet objectToLdTaclet(ArrayList<Field> fields, ArrayList<Sort> sorts, ArrayList<String> names,
                                           ArrayList<KeYJavaType> types,
                                           KeYJavaType ldkjt, Function objectToLdFun, Function constructorFun) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setName(new Name("object2" + ldkjt.getName()));
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

    /**
     * Generates a taclet which expresses when two ledger data objects are equal.
     * @param ldSort the sort for which the taclet is generated
     * @param getters the getter functions of that sort
     * @return the equals taclet
     */
    private RewriteTaclet equalsTaclet(Sort ldSort, ArrayList<Function> getters) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setName(new Name("equals" + ldSort.name()));
        SchemaVariable ldVar1 = SchemaVariableFactory.createTermSV(new Name("ld1"), ldSort);
        SchemaVariable ldVar2 = SchemaVariableFactory.createTermSV(new Name("ld2"), ldSort);
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

    /**
     * Generates a getter taclet, for a given field of a given Type.
     * @param i the index to the list of fields/names
     * @param schemaVars the field schema variables
     * @param getters the other getter functions
     * @param ldkjt the {@link KeYJavaType} for which the taclet is generated
     * @param shortFieldName a short and pretty name to make the result well-formed
     * @param constructorFun the constructor function for this type
     * @return the getter taclet
     */
    private RewriteTaclet createGetterTaclet(int i, List<SchemaVariable> schemaVars,
                                             List<Function> getters, KeYJavaType ldkjt, String shortFieldName, Function constructorFun) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        Term[] varTerms = new Term[schemaVars.size()];
        for (int j = 0; j < schemaVars.size(); ++j) {
            varTerms[j] = termBuilder.var(schemaVars.get(j));
        }
        tacletBuilder.setName(new Name(shortFieldName + "OfNew" + ldkjt.getName()));
        Term findTerm = termBuilder.func(getters.get(i), termBuilder.func(constructorFun, varTerms));
        tacletBuilder.setFind(findTerm);
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        tacletBuilder.addRuleSet(SIMPLIFY);
        Term replaceWithTerm = termBuilder.var(schemaVars.get(i));
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));
        return tacletBuilder.getTaclet();
    }

    /**
     * returns the sort's child sorts among the given set of sorts
     * @param s the given sort
     * @param sorts the set of possible children
     * @return all child sorts
     */
    private Set<Sort> childSorts(Sort s, Collection<Sort> sorts) {
        Set<Sort> res = new HashSet<>();
        for (Sort child : sorts) {
            if (!(child instanceof NullSort) && !child.equals(s) && child.extendsTrans(s)) {
                res.add(child);
            }
        }
        return res;
    }

    /**
     * The serialization method is only specified for the LedgerData supertype. In order to extend this specification
     * to all subtypes, this taclet can be used.
     * @param kjt the {@link KeYJavaType} for which the taclet is generated
     * @param serFun the serialization function for this type
     * @param o2DFun the object2Data function for this type
     * @return the serialization extension taclet
     */
    private RewriteTaclet serializationExtensionTaclet(KeYJavaType kjt, Function serFun, Function o2DFun) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setName(new Name("extendSerializationTo" + kjt.getSort().name()));
        SchemaVariable ldVar1 = SchemaVariableFactory.createTermSV(new Name("ld"), superSort);
        SchemaVariable heapVar = SchemaVariableFactory.createTermSV(new Name("h"), heapSort);
        Term findTerm = termBuilder.func(superSerFun, termBuilder.func(superObjectToLdFun, termBuilder.var(heapVar), termBuilder.var(ldVar1)));
        tacletBuilder.setFind(findTerm);
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        Term replaceWithTerm = termBuilder.func(serFun, termBuilder.func(o2DFun, termBuilder.var(heapVar), termBuilder.var(ldVar1)));
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));
        return tacletBuilder.getTaclet();
    }

    /**
     * The deserialization method is only specified for the LedgerData supertype. In order to extend this specification
     * to all subtypes, this taclet can be used.
     * @param kjt the {@link KeYJavaType} for which the taclet is generated
     * @param deserFun the deserialization function for this type
     * @param o2DFun the object2Data function for this type
     * @return the deserialization extension taclet
     */
    private RewriteTaclet deserializationExtensionTaclet(KeYJavaType kjt, Function deserFun, Function o2DFun) {
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        tacletBuilder.setName(new Name("extendDeserializationTo" + kjt.getSort().name()));
        SchemaVariable var1 = SchemaVariableFactory.createTermSV(new Name("x"), superSort);
        SchemaVariable var2 = SchemaVariableFactory.createTermSV(new Name("y"), superSort);
        SchemaVariable heapVar = SchemaVariableFactory.createTermSV(new Name("h"), heapSort);
        Term o2dTerm = termBuilder.func(superObjectToLdFun, termBuilder.var(heapVar), termBuilder.var(var1));
        Term deserOfArrayTerm = termBuilder.func(superDeserFun, termBuilder.func(a2sFun, termBuilder.var(heapVar), termBuilder.var(var2)));
        Term findTerm = termBuilder.equals(o2dTerm, deserOfArrayTerm);
        tacletBuilder.setFind(findTerm);
        tacletBuilder.setApplicationRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
        Term newO2dTerm = termBuilder.func(o2DFun, termBuilder.var(heapVar), termBuilder.var(var1));
        Term newDeserOfArrayTerm = termBuilder.func(deserFun, termBuilder.func(a2sFun, termBuilder.var(heapVar), termBuilder.var(var2)));
        Term replaceWithTerm = termBuilder.equals(newO2dTerm, newDeserOfArrayTerm);
        tacletBuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(replaceWithTerm));
        return tacletBuilder.getTaclet();
    }

    public ArrayList<Function> getNewFunctions() {
        return newFunctions;
    }
}