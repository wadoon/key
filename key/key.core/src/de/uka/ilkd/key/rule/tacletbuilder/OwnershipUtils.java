package de.uka.ilkd.key.rule.tacletbuilder;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ImplicitFieldSpecification;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.MiscTools;

/**
 * This class provides static method for generating Ownership taclets.
 *
 * @author Wolfram Pfeifer
 */
public final class OwnershipUtils {
    // TODO: better use another heuristic?
    /* inReachableStateImplication seems to be a good choice:
     * It is ensured that the resulting formula does not occur on the sequence. */
    private static final RuleSet HEURISTICS = new RuleSet(new Name("inReachableStateImplication"));

    private OwnershipUtils() { };

    private static boolean isImplicitField(Field f) {
        return f instanceof ImplicitFieldSpecification;
    }

    private static boolean isPrimitiveField(Field f) {
        Type t = f.getType();
        if (t instanceof KeYJavaType) {
            KeYJavaType kjt = (KeYJavaType)t;
            return kjt.getJavaType() instanceof PrimitiveType;
        }
        return false;
    }

    private static boolean isRep(Field f) {
        return f.getProgramName().startsWith("rep_");
    }

    private static boolean isPeer(Field f) {
        return f.getProgramName().startsWith("peer_");
    }

    private static ImmutableList<Field> collectAllExplicitReferenceMembers(ProgramVariable selfVar,
            Services services) {
        KeYJavaType kjt = selfVar.getKeYJavaType();
        ImmutableList<Field> fields = ImmutableSLList.<Field>nil();

        ImmutableList<KeYJavaType> superTypes = services.getJavaInfo().getAllSupertypes(kjt);

        for (KeYJavaType st : superTypes) {
            Type t = st.getJavaType();
            if (t instanceof TypeDeclaration) {
                // TODO: respect visibility!
                fields = fields.prepend(services.getJavaInfo().getAllFields((TypeDeclaration)t));
            }
        }

        // filter implicit and primitive type fields
        List<Field> tmp = fields.stream()
                .filter(x -> !isImplicitField(x))
                .filter(x -> !isPrimitiveField(x))
                .collect(Collectors.toList());
        ImmutableList<Field> filtered = ImmutableSLList.<Field>nil().prepend(tmp);

        return filtered;
    }

    private static Taclet createDisjointnessTaclet(Services services, ProgramVariable selfVar) {
        // more generic than first version: can be used for objects which are not stored in fields
        // TODO: maybe use varcond differentFields here?
        /* disjFP {
         *     \schemaVariable \term Object o, r1, r2;
         *     \schemaVariable \term Heap h;
         *     \assumes(owner(r1) = o)
         *     \assumes(owner(r2) = o)
         *     \find(r1.repfp@h)
         *     \add (r1 != null & r2 != null & r1 != r2
         *     -> \disjoint(r1.repfp@h, r2.repfp@h) ==>)
         * };
         */

        TermBuilder tb = services.getTermBuilder();

        Name heapName = new Name("heap");
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        SchemaVariable heapSV = SchemaVariableFactory.createTermSV(heapName, heapSort);

        Name oName = new Name("o");
        Name r1Name = new Name("r1");
        Name r2Name = new Name("r2");
        Sort objectSort = services.getJavaInfo().getJavaLangObject().getSort();
        SchemaVariable oSV = SchemaVariableFactory.createTermSV(oName, objectSort);
        SchemaVariable r1SV = SchemaVariableFactory.createTermSV(r1Name, objectSort);
        SchemaVariable r2SV = SchemaVariableFactory.createTermSV(r2Name, objectSort);

        Function repFP = services.getNamespaces().functions().lookup("java.lang.Object::$repfp");
        Function owner = services.getNamespaces().functions().lookup("owner");

        Term assume1 = tb.equals(tb.func(owner, tb.var(r1SV)), tb.var(oSV));
        Term assume2 = tb.equals(tb.func(owner, tb.var(r2SV)), tb.var(oSV));

        // accumulate precondition, i.e. left side of implication
        Term pre = tb.not(tb.equals(tb.var(r1SV), tb.NULL()));              // r1 != null
        pre = tb.and(pre, tb.not(tb.equals(tb.var(r2SV), tb.NULL())));      // r2 != null
        pre = tb.and(pre, tb.not(tb.equals(tb.var(r1SV), tb.var(r2SV))));   // r1 != r2

        Term fp1 = tb.func(repFP, tb.var(heapSV), tb.var(r1SV));            // r1.repfp
        Term fp2 = tb.func(repFP, tb.var(heapSV), tb.var(r2SV));            // r2.repfp

        Term disj = tb.disjoint(fp1, fp2);                                  // r1.repfp # r2.repfp
        Term add = tb.imp(pre, disj);

        // we have our term, now create the taclet
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();
        //NoFindTacletBuilder tacletBuilder = new NoFindTacletBuilder();

        Name name = MiscTools.toValidTacletName("rep footprints disjoint");
        tacletBuilder.setName(name);

        ImmutableSet<Choice> choices = DefaultImmutableSet.<Choice>nil()
                .add(new Choice("Java", "programRules"));
        tacletBuilder.setChoices(choices);

        tacletBuilder.addRuleSet(HEURISTICS);

        // we search for r1.repfp (this makes it unnecessary to manually instantiate the heap)
        tacletBuilder.setFind(fp1);

        // \assume
        SequentFormula sf1 = new SequentFormula(assume1);
        SequentFormula sf2 = new SequentFormula(assume2);
        Semisequent semiAssume = Semisequent.EMPTY_SEMISEQUENT
                                            .insertFirst(sf1).semisequent()
                                            .insertFirst(sf2).semisequent();
        tacletBuilder.setIfSequent(Sequent.createAnteSequent(semiAssume));

        // \add
        SequentFormula seqFormula = new SequentFormula(add);
        Semisequent semi = new Semisequent(seqFormula);
        Sequent seq = Sequent.createAnteSequent(semi);
        tacletBuilder.addTacletGoalTemplate(
                new TacletGoalTemplate(seq, ImmutableSLList.<Taclet>nil()));

        return tacletBuilder.getTaclet();
    }

    private static List<Taclet> createFootprintsRepresentsClauses(Services services,
            ProgramVariable selfVar) {
        /* repfp_self {
         *   \schemaVar \term Heap H;
         *   \find(repfp(H, self))
         *   \replacewith(allFields(H, self)
         *      union (
         *          if (Object::select(h, Object::select(h, self, f), created) = TRUE)
         *          then (Object::select(h, self, f)))
         *          else empty;
         *      union ( ... );
         * };
         */

        List<Taclet> result = new ArrayList<>();

        ImmutableList<Field> fields = collectAllExplicitReferenceMembers(selfVar, services);

        TermBuilder tb = services.getTermBuilder();

        // start with allFields(self)
        Term replaceRepfp = tb.allFields(tb.var(selfVar));
        Term replacePeerfp = tb.allFields(tb.var(selfVar));

        // for every field we add: self.f.created = TRUE ? relinv(self.f) : empty
        Name heapName = new Name("heap");
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        SchemaVariable heapSV = SchemaVariableFactory.createTermSV(heapName, heapSort);

        Function repFP = services.getNamespaces()
                                      .functions()
                                      .lookup("java.lang.Object::$repfp");
        Function peerFP = services.getNamespaces()
                .functions()
                .lookup("java.lang.Object::$peerfp");

        Term findRepfp = tb.func(repFP, tb.var(heapSV), tb.var(selfVar));
        Term findPeerfp = tb.func(peerFP, tb.var(heapSV), tb.var(selfVar));

        for (Field f : fields) {

            if (isRep(f)) {
                ProgramVariable pvF = services.getJavaInfo().getAttribute(f.getFullName());
                Sort fSort = f.getProgramVariable().sort();

                // assert pvF instanceof LocationVariable;
                Function fieldSymbol = services.getTypeConverter()
                                               .getHeapLDT()
                                               .getFieldSymbolForPV((LocationVariable)pvF,
                                                                    services);

                // "self.f": Object::select(heapSV, self, f)
                Term oF = tb.select(fSort, tb.var(heapSV), tb.var(selfVar), tb.func(fieldSymbol));

                // self.f.created = TRUE
                Term oFCreated = tb.created(oF);

                // repfp(self.f)
                Term repfpOF = tb.func(repFP, tb.var(heapSV), oF);

                replaceRepfp = tb.union(replaceRepfp, tb.ife(oFCreated, repfpOF, tb.empty()));
            } else if (isPeer(f)) {
                ProgramVariable pvF = services.getJavaInfo().getAttribute(f.getFullName());
                Sort fSort = f.getProgramVariable().sort();

                // assert pvF instanceof LocationVariable;
                Function fieldSymbol = services.getTypeConverter()
                                               .getHeapLDT()
                                               .getFieldSymbolForPV((LocationVariable)pvF,
                                                                    services);

                // "self.f": Object::select(heapSV, self, f)
                Term oF = tb.select(fSort, tb.var(heapSV), tb.var(selfVar), tb.func(fieldSymbol));

                // self.f.created = TRUE
                Term oFCreated = tb.created(oF);

                // peerfp(self.f)
                Term peerfpOF = tb.func(peerFP, tb.var(heapSV), oF);

                replacePeerfp = tb.union(replacePeerfp, tb.ife(oFCreated, peerfpOF, tb.empty()));
            }
        }

        // we have our terms, now create the taclets
        RewriteTacletBuilder<RewriteTaclet> tacletBuilderRepfp = new RewriteTacletBuilder<>();
        RewriteTacletBuilder<RewriteTaclet> tacletBuilderPeerfp = new RewriteTacletBuilder<>();

        // generate taclet names
        String nameRepfp = "represents axiom for " + selfVar.sort() + ".repfp";
        tacletBuilderRepfp.setName(MiscTools.toValidTacletName(nameRepfp));

        String namePeerfp = "represents axiom for " + selfVar.sort() + ".peerfp";
        tacletBuilderPeerfp.setName(MiscTools.toValidTacletName(namePeerfp));

        ImmutableSet<Choice> choices = DefaultImmutableSet.<Choice>nil()
                .add(new Choice("Java", "programRules"));
        tacletBuilderRepfp.setChoices(choices);
        tacletBuilderPeerfp.setChoices(choices);

        tacletBuilderRepfp.addRuleSet(HEURISTICS);
        tacletBuilderPeerfp.addRuleSet(HEURISTICS);

        // TODO: boolean observer function as predicate? -> shorter syntax
        // TODO: term labels?
        tacletBuilderRepfp.setFind(findRepfp);
        tacletBuilderPeerfp.setFind(findPeerfp);

        // \replacewith
        tacletBuilderRepfp.addTacletGoalTemplate(
                new RewriteTacletGoalTemplate(replaceRepfp));
        tacletBuilderPeerfp.addTacletGoalTemplate(
                new RewriteTacletGoalTemplate(replacePeerfp));

        Taclet tacletRepfp = tacletBuilderRepfp.getTaclet();
        Taclet tacletPeerfp = tacletBuilderPeerfp.getTaclet();

        result.add(tacletRepfp);
        result.add(tacletPeerfp);
        return result;
    }

    private static Taclet createRelinvRepresentsClause(Services services, ProgramVariable selfVar) {
        /* relinv_self {
         *   \schemaVar \term Heap H;
         *   \find(relinv(H, self))
         *   \replacewith(inv(H, self)
         *                            // quantifier not explicit, instead we roll out for all fields
         *      && (\forall Field f;
         *          Object::select(h, Object::select(h, self, f), created) = TRUE
         *          -> relinv(Object::select(h, self, f)));
         * };
         */

        // generate represents clauses for relinv for self
        // (concrete invariant is hidden for all objects != self)
        ImmutableList<Field> fields = collectAllExplicitReferenceMembers(selfVar, services);

        TermBuilder tb = services.getTermBuilder();

        // start with invariant(self)
        Term replace = tb.inv(tb.var(selfVar));

        // for every field we add: self.f.created = TRUE -> relinv(self.f)
        Name heapName = new Name("heap");
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        SchemaVariable heapSV = SchemaVariableFactory.createTermSV(heapName, heapSort);

        Function relinvFunc = services.getNamespaces()
                                      .functions()
                                      .lookup("java.lang.Object::$relinv");

        Term find = tb.func(relinvFunc, tb.var(heapSV), tb.var(selfVar));

        for (Field f : fields) {

            // collect terms of the form:
            // o.f.created = TRUE -> relinv(o.f)

            ProgramVariable pvF = services.getJavaInfo().getAttribute(f.getFullName());
            Sort fSort = f.getProgramVariable().sort();

            // assert pvF instanceof LocationVariable;
            Function fieldSymbol = services.getTypeConverter()
                                           .getHeapLDT()
                                           .getFieldSymbolForPV((LocationVariable)pvF, services);

            // "self.f": Object::select(heapSV, self, f)
            Term oF = tb.select(fSort, tb.var(heapSV), tb.var(selfVar), tb.func(fieldSymbol));

            // self.f.created = TRUE
            Term oFCreated = tb.created(oF);

            // relinv(self.f)
            Term relinvOF = tb.func(relinvFunc, tb.var(heapSV), oF);

            replace = tb.and(replace, tb.imp(oFCreated, tb.convertToFormula(relinvOF)));
        }

        // we have our terms, now create the taclet
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();

        // generate taclet name
        String name = "represents axiom for " + selfVar.sort() + ".relinv";
        tacletBuilder.setName(MiscTools.toValidTacletName(name));

        ImmutableSet<Choice> choices = DefaultImmutableSet.<Choice>nil()
                .add(new Choice("Java", "programRules"));
        tacletBuilder.setChoices(choices);

        tacletBuilder.addRuleSet(HEURISTICS);

        // \find("o.f")
        // TODO: boolean observer function as predicate? -> shorter syntax
        // TODO: term labels?
        tacletBuilder.setFind(tb.convertToFormula(find));

        // \replacewith
        tacletBuilder.addTacletGoalTemplate(
                new RewriteTacletGoalTemplate(tb.convertToFormula(replace)));

        Taclet taclet = tacletBuilder.getTaclet();
        return taclet;
    }

    private static List<Taclet> createOwnershipTaclets(Services services, ProgramVariable selfVar) {
        ImmutableList<Field> fields = collectAllExplicitReferenceMembers(selfVar, services);
        List<Taclet> result = new ArrayList<>();
        for (Field f : fields) {

            // generate taclets for rep and peer fields
            if (isRep(f)) {
                result.add(createOwnershipAxiomTaclet(f, true, services));
            } else if (isPeer(f)) {
                result.add(createOwnershipAxiomTaclet(f, false, services));
            }
        }
        return result;
    }

    private static Taclet createOwnershipAxiomTaclet(Field f, boolean isRep, Services services) {
        /* rep {
         *   \schemaVar \term Object o;
         *   \schemaVar \term Heap heapSV;
         *   \find(Object::select(heapSV, o, f))
         *   \add(Object::select(heapSV, o, f) != null -> owner(Object::select(heapSV, o, f)) == o)
         * };
         */

        Name heapName = new Name("h");
        Name objName = new Name("o");

        Sort oSort = services.getJavaInfo().getJavaLangObject().getSort();
        Sort fSort = f.getProgramVariable().sort();

        SchemaVariable svH = SchemaVariableFactory.createTermSV(heapName,
                services.getTypeConverter().getHeapLDT().targetSort());
        SchemaVariable svO = SchemaVariableFactory.createTermSV(objName, oSort);

        // since we have a concrete known field, we need a ProgramVariable here
        ProgramVariable pvF = services.getJavaInfo().getAttribute(f.getFullName());

        // assert pvF instanceof LocationVariable;
        Function fieldSymbol = services.getTypeConverter()
                                       .getHeapLDT()
                                       .getFieldSymbolForPV((LocationVariable)pvF, services);

        TermBuilder tb = services.getTermBuilder();

        // "o.f": Object::select(heapSV, o, f)
        Term oF = tb.select(fSort, tb.var(svH), tb.var(svO), tb.func(fieldSymbol));

        Function func = services.getNamespaces().functions().lookup("owner");
        Term own = tb.func(func, oF);
        Term right;
        if (isRep) {
            // owner("o.f") = o
            right = tb.var(svO);
        } else {
            // owner("o.f") = owner(o)
            right = tb.func(func, tb.var(svO));
        }
        Term eq = tb.equals(own, right);

        // "o.f" =! null
        Term notNull = tb.not(tb.equals(oF, tb.NULL()));

        SequentFormula seqFormula = new SequentFormula(tb.imp(notNull, eq));
        Semisequent semi = new Semisequent(seqFormula);
        Sequent seq = Sequent.createAnteSequent(semi);

        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();

        // generate taclet name
        String name = (isRep ? "rep" : "peer") + " axiom for " + f.getProgramName();
        tacletBuilder.setName(MiscTools.toValidTacletName(name));

        ImmutableSet<Choice> choices = DefaultImmutableSet.<Choice>nil()
                .add(new Choice("Java", "programRules"));
        tacletBuilder.setChoices(choices);

        // \find("o.f")
        tacletBuilder.setFind(oF);

        tacletBuilder.addRuleSet(HEURISTICS);

        // \add(Object::select(heapSV, o, f) != null -> owner(Object::select(heapSV, o, f)) = o ==>)
        tacletBuilder.addTacletGoalTemplate(
                new TacletGoalTemplate(seq, ImmutableSLList.<Taclet>nil()));
        return tacletBuilder.getTaclet();
    }

    /**
     * Creates all Ownership taclets that can be used in a proof with the given self variable.
     * @param proofServices the Services of the proof
     * @param selfVar the current "self" of the PO
     *          (needed for determining which taclets to generate)
     * @return the immutable set of all created taclets (those taclets have to be registered!)
     */
    public static ImmutableSet<Taclet> createTaclets(Services proofServices,
            ProgramVariable selfVar) {

        ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();

        // add ownership axioms for rep/peer fields defined in the class containing the contract
        // TODO: what about ownership of fields in other classes?
        for (Taclet t : createOwnershipTaclets(proofServices, selfVar)) {
            result = result.add(t);
        }

        // add represents axioms for relinv
        result = result.add(createRelinvRepresentsClause(proofServices, selfVar));

        // add represents axioms for footprints
        for (Taclet t : createFootprintsRepresentsClauses(proofServices, selfVar)) {
            result = result.add(t);
        }

        // add disjointness taclet for rep footprints
        result = result.add(createDisjointnessTaclet(proofServices, selfVar));

        return result;
    }
}
