package de.uka.ilkd.key.rule.tacletbuilder;

import java.util.ArrayList;
import java.util.List;

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

    private static List<Taclet> createDisjointFPTaclets(Services services,
            ProgramVariable selfVar) {
        /* for each pair (f1, f2) of rep fields declared in this class (or a superclass!)
         * we add a taclet of the following form
         * disjFP {
         *     \schemaVar \term Heap h;
         *     \find();         // TODO: two find clauses possible? -> only if f1.repfp appears
         *     \add(f1 != null & f2 != null -> f1.repfp # f2.repfp);
         * };
         */

        List<Taclet> taclets = new ArrayList<>();

        ImmutableList<Field> fields = services.getJavaInfo().getAllFields(
                (TypeDeclaration) selfVar.getKeYJavaType().getJavaType());
        ImmutableList<Field> rest = fields;

        for (Field f1 : fields) {
            rest = rest.tail();

            // skip implicit fields and fields with primitive type
            if (isImplicitField(f1) || isPrimitiveField(f1)) {
                continue;
            }

            // skip non-rep fields
            if (!isRep(f1)) {
                continue;
            }
            for (Field f2 : rest) {
                // skip implicit fields and fields with primitive type
                if (isImplicitField(f2) || isPrimitiveField(f2)) {
                    continue;
                }

                // skip non-rep fields
                if (!isRep(f2)) {
                    continue;
                }

                taclets.add(createDisjointnessTaclet(f1, f2, services, selfVar));
            }
        }
        return taclets;
    }

    // TODO: do we need the symmetrical variant of the taclet as well?
    // (may have to do with find term)
    private static Taclet createDisjointnessTaclet(Field f1, Field f2, Services services,
            ProgramVariable selfVar) {

        TermBuilder tb = services.getTermBuilder();

        Name heapName = new Name("heap");
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        SchemaVariable heapSV = SchemaVariableFactory.createTermSV(heapName, heapSort);

        Function repFP = services.getNamespaces()
                .functions()
                .lookup("java.lang.Object::$repfp");
        ProgramVariable pvF1 = services.getJavaInfo().getAttribute(f1.getFullName());
        ProgramVariable pvF2 = services.getJavaInfo().getAttribute(f2.getFullName());
        Sort f1Sort = f1.getProgramVariable().sort();
        Sort f2Sort = f2.getProgramVariable().sort();

        Function fieldSymbol1 = services.getTypeConverter()
                .getHeapLDT()
                .getFieldSymbolForPV((LocationVariable)pvF1, services);
        Function fieldSymbol2 = services.getTypeConverter()
                .getHeapLDT()
                .getFieldSymbolForPV((LocationVariable)pvF2, services);

        Term oF1 = tb.select(f1Sort, tb.var(heapSV), tb.var(selfVar), tb.func(fieldSymbol1));
        Term oF2 = tb.select(f2Sort, tb.var(heapSV), tb.var(selfVar), tb.func(fieldSymbol2));

        Term fp1 = tb.func(repFP, tb.var(heapSV), oF1);
        Term fp2 = tb.func(repFP, tb.var(heapSV), oF2);

        Term nonNullF1 = tb.not(tb.equals(oF1, tb.NULL()));
        Term nonNullF2 = tb.not(tb.equals(oF2, tb.NULL()));
        Term disj = tb.disjoint(fp1, fp2);
        Term add = tb.imp(tb.and(nonNullF1, nonNullF2), disj);

        // we have our term, now create the taclet
        RewriteTacletBuilder<RewriteTaclet> tacletBuilder = new RewriteTacletBuilder<>();

        Name name = MiscTools.toValidTacletName("repfp disjoint " + f1 + " " + f2);
        tacletBuilder.setName(name);

        ImmutableSet<Choice> choices = DefaultImmutableSet.<Choice>nil()
                .add(new Choice("Java", "programRules"));
        tacletBuilder.setChoices(choices);

        // TODO: better use another heuristic?
        tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));

        // we search for self.f1.repfp (this makes it unnecessary to manually instantiate the heap)
        tacletBuilder.setFind(fp1);

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

        // TODO: does this include inherited fields?
        ImmutableList<Field> fields = services.getJavaInfo().getAllFields(
                (TypeDeclaration) selfVar.getKeYJavaType().getJavaType());

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
            // skip implicit fields
            if (isImplicitField(f)) {
                continue;
            }

            if (isPrimitiveField(f)) {
                continue;
            }

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

        // TODO: better use another heuristic?
        tacletBuilderRepfp.addRuleSet(new RuleSet(new Name("simplify")));
        tacletBuilderPeerfp.addRuleSet(new RuleSet(new Name("simplify")));

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
        ImmutableList<Field> fields = services.getJavaInfo().getAllFields(
                (TypeDeclaration) selfVar.getKeYJavaType().getJavaType());

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
            // skip implicit fields
            if (isImplicitField(f)) {
                continue;
            }

            // skip primitive fields
            if (isPrimitiveField(f)) {
                continue;
            }

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

        // TODO: better use another heuristic?
        tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));

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

    private static List<Taclet> createOwnershipTaclets(Services proofServices,
            ProgramVariable selfVar) {
        ImmutableList<Field> fields = proofServices.getJavaInfo().getAllFields(
                (TypeDeclaration) selfVar.getKeYJavaType().getJavaType());
        List<Taclet> result = new ArrayList<>();
        for (Field f : fields) {

            // generate taclets for rep and peer fields
            if (isRep(f)) {
                result.add(createOwnershipAxiomTaclet(f, true, proofServices));
            } else if (isPeer(f)) {
                result.add(createOwnershipAxiomTaclet(f, false, proofServices));
            }
        }
        return result;
    }

    private static Taclet createOwnershipAxiomTaclet(Field f, boolean isRep,
            Services services) {
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

        // TODO: better use another heuristic?
        tacletBuilder.addRuleSet(new RuleSet(new Name("simplify")));

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

        // for each pair of rep fields: create disjointness taclet
        for (Taclet t : createDisjointFPTaclets(proofServices, selfVar)) {
            result = result.add(t);
        }

        return result;
    }
}
