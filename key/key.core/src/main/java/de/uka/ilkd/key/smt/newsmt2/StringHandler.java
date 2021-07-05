package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.io.IOException;
import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;

public class StringHandler implements SMTHandler {

    public static final Type STRING = new Type("String", "s2u", "u2s");
    private static final Type INT = IntegerOpHandler.INT;
    private static final Type BOOL = Type.BOOL;

    private static <T> List<T> reorder(List<T> xs, int... newIndices) {
        assert newIndices.length == xs.size();
        List<T> reordered = new ArrayList<>(xs);
        for (int i = 0; i < newIndices.length; i++) {
            reordered.set(newIndices[i], xs.get(i));
        }
        return reordered;
    }

    @FunctionalInterface
    private interface Translator {
        SExpr translate(List<SExpr> translatedSubs);
    }

    private static class O {
        private Operator op;
        private Name name;
        private Translator translator;

        private O(Operator op, Translator translator) {
            this.op = op;
            this.translator = translator;
        }

        private O(Name name, Translator translator) {
            this.name = name;
            this.translator = translator;
        }

        private static List<SExpr> charValuesToString(List<SExpr> subs, int... charValueIndices) {
            List<SExpr> convertedSubs = new ArrayList<>(subs);
            for (int idx : charValueIndices) {
                convertedSubs.set(idx, new SExpr("str.from_code", STRING, subs.get(idx)));
            }
            return convertedSubs;
        }

        private static SExpr stringToCharValue(SExpr str) {
            return new SExpr("str.to_code", INT, Arrays.asList(str));
        }

        private static O strContent() {
            return new O(CharListLDT.STRINGCONTENT_NAME, translatedSubs ->
                translatedSubs.get(0));
        }

        private static O strPool() {
            return new O(CharListLDT.STRINGPOOL_NAME, translatedSubs ->
                    translatedSubs.get(0));
        }

        private static O startsWith(CharListLDT stringLDT) {
            return new O(stringLDT.getClStartsWith(), translatedSubs ->
                new SExpr("str.prefixof", BOOL, translatedSubs));
        }

        private static O endsWith(CharListLDT stringLDT) {
            return new O(stringLDT.getClEndsWith(), translatedSubs ->
                new SExpr("str.suffixof", BOOL, translatedSubs));
        }

        private static O indexOf(CharListLDT stringLDT) {
            return new O(stringLDT.getClIndexOfCl(), translatedSubs ->
                new SExpr("str.indexof", INT, reorder(translatedSubs, 0, 2, 1)));
        }

        private static O indexOfChar(CharListLDT stringLDT) {
            return new O(stringLDT.getClIndexOfChar(), translatedSubs ->
                new SExpr("str.indexof", INT, charValuesToString(translatedSubs, 1)));
        }

        private static O replace(CharListLDT stringLDT) {
            return new O(stringLDT.getClReplace(), translatedSubs ->
                new SExpr("str.replace_all", STRING, charValuesToString(translatedSubs, 1, 2)));
        }

        private static O substring(SeqLDT seqLDT) {
            return new O(seqLDT.getSeqSub(), translatedSubs ->
                new SExpr("str.substr", STRING, translatedSubs));
        }

        private static O length(SeqLDT seqLDT) {
            return new O(seqLDT.getSeqLen(), translatedSubs ->
                new SExpr("str.len", INT, translatedSubs));
        }

        private static O concat(SeqLDT seqLDT) {
            return new O(seqLDT.getSeqConcat(), translatedSubs ->
                new SExpr("str.++", STRING, translatedSubs));
        }

        private static O equals() {
            return new O(Equality.EQUALS, translatedSubs ->
                new SExpr("=", BOOL, translatedSubs));
        }

        private static O charAt(SeqLDT seqLDT, IntegerLDT intLDT, Services services) {
            return new O(seqLDT.getSeqGet(intLDT.targetSort(), services), translatedSubs ->
                    stringToCharValue(new SExpr("str.at", STRING, translatedSubs)));
        }

        private boolean matches(Term t) {
            // I refuse to use the visitor pattern for a sum type with two elements.
            assert (op == null || name == null) && (op != null || name != null);
            if (name == null) {
                return t.op().equals(op);
            }
            return t.op().name().equals(name);
        }

        private SExpr translate(List<SExpr> translatedSubs) {
            return translator.translate(translatedSubs);
        }
    }

    private static class LeafHandler {
        private BiFunction<MasterHandler, Term, SExpr> handle;
        private Function<Term, Boolean> canHandle;

        private LeafHandler(BiFunction<MasterHandler, Term, SExpr> handle, Function<Term, Boolean> canHandle) {
            this.handle = handle;
            this.canHandle = canHandle;
        }

        private SExpr handle(MasterHandler h, Term term) {
            return handle.apply(h, term);
        }

        private boolean canHandle(Term term) {
            return canHandle.apply(term);
        }
    }

    private static class H {
        private O op;
        private LeafHandler leafHandler;
        private List<H> subHandlers;

        private H(O op, LeafHandler leafHandler, List<H> subHandlers) {
            this.op = op;
            this.leafHandler = leafHandler;
            this.subHandlers = subHandlers;
        }

        private static H inner(O op, H... subHandlers) {
            return new H(op, null, Arrays.asList(subHandlers));
        }

        private static H leaf(BiFunction<MasterHandler, Term, SExpr> handle, Function<Term, Boolean> canHandle) {
            return new H(null, new LeafHandler(handle, canHandle), null);
        }

        private static H leaf(Type type) {
            return leaf((h, term) -> h.translate(term, type), term -> true);
        }

        private static H startsWith(CharListLDT stringLDT) {
            return H.inner(O.startsWith(stringLDT),
                    H.inner(O.strContent(), H.leaf(STRING)),
                    H.inner(O.strContent(), H.leaf(STRING)));
        }

        private static H endsWith(CharListLDT stringLDT) {
            return H.inner(O.endsWith(stringLDT),
                    H.inner(O.strContent(), H.leaf(STRING)),
                    H.inner(O.strContent(), H.leaf(STRING)));
        }

        private static H indexOf(CharListLDT stringLDT) {
            return H.inner(O.indexOf(stringLDT),
                    H.inner(O.strContent(), H.leaf(STRING)),
                    H.leaf(INT),
                    H.inner(O.strContent(), H.leaf(STRING)));
        }

        private static H indexOfChar(CharListLDT stringLDT) {
            return H.inner(O.indexOfChar(stringLDT),
                    H.inner(O.strContent(), H.leaf(STRING)),
                    H.leaf(INT),
                    H.leaf(INT));
        }

        private static H replace(CharListLDT stringLDT) {
            return H.inner(O.equals(),
                    H.inner(O.strContent(), H.leaf(STRING)),
                    H.inner(O.replace(stringLDT),
                            H.inner(O.strContent(), H.leaf(STRING)),
                            H.leaf(INT),
                            H.leaf(INT)));
        }

        private static H substring(SeqLDT seqLDT) {
            return H.inner(O.equals(),
                    H.inner(O.strContent(), H.leaf(STRING)),
                    H.inner(O.substring(seqLDT),
                            H.inner(O.strContent(), H.leaf(STRING)),
                            H.leaf(INT),
                            H.leaf(INT)));
        }

        private static H length(SeqLDT seqLDT) {
            return H.inner(O.length(seqLDT),
                    H.inner(O.strContent(), H.leaf(STRING)));
        }

        private static H concat(SeqLDT seqLDT) {
            return H.inner(O.equals(),
                    H.inner(O.strContent(), H.leaf(STRING)),
                    H.inner(O.concat(seqLDT),
                            H.inner(O.strContent(), H.leaf(STRING)),
                            H.inner(O.strContent(), H.leaf(STRING))));
        }

        private static Boolean canHandleLiteralDecl(SeqLDT seqLDT, Term term) {
            if (term.op().equals(seqLDT.getSeqSingleton())) {
                return true;
            }
            if (!term.op().equals(seqLDT.getSeqConcat())) {
                return false;
            }
            return canHandleLiteralDecl(seqLDT, term.sub(0)) && canHandleLiteralDecl(seqLDT, term.sub(1));
        }

        private static SExpr handleLiteralDecl(SeqLDT seqLDT, MasterHandler h, Term term) {
            if (term.op().equals(seqLDT.getSeqSingleton())) {
                return new SExpr("str.from_code", STRING, h.translate(term.sub(0), INT));
            }
            SExpr left = handleLiteralDecl(seqLDT, h, term.sub(0));
            SExpr right = handleLiteralDecl(seqLDT, h, term.sub(1));
            return new SExpr("str.++", STRING, left, right);
        }


        private static H literals(SeqLDT seqLDT) {
            return H.inner(O.strPool(), H.leaf(
                    (h, term) -> handleLiteralDecl(seqLDT, h, term),
                    term -> canHandleLiteralDecl(seqLDT, term)));
        }

        private static H charAt(SeqLDT seqLDT, IntegerLDT intLDT, Services services) {
            return H.inner(O.charAt(seqLDT, intLDT, services),
                    H.inner(O.strContent(), H.leaf(STRING)),
                    H.leaf(INT));
        }

        private boolean isLeaf() {
            return op == null;
        }

        private boolean canHandle(Term t) {
            if (isLeaf()) {
                return leafHandler.canHandle(t);
            }
            if (!op.matches(t)) {
                return false;
            }
            assert t.subs().size() == subHandlers.size();
            for (int i = 0; i < subHandlers.size(); i++) {
                if (!subHandlers.get(i).canHandle(t.sub(i))) {
                    return false;
                }
            }
            return true;
        }

        private SExpr handle(MasterHandler h, Term term) throws SMTTranslationException {
            if (isLeaf()) {
                return leafHandler.handle(h, term);
            }
            List<SExpr> translatedSubs = new ArrayList<>();
            assert term.subs().size() == subHandlers.size();
            for (int i = 0; i < subHandlers.size(); i++) {
                // We don't need to coerce inner nodes. We already
                // ensure that they have the right type by construction.
                translatedSubs.add(subHandlers.get(i).handle(h, term.sub(i)));
            }
            return op.translate(translatedSubs);
        }
    }

    private final List<H> handlers = new ArrayList<>();

    @Override
    public void init(MasterHandler h, Services services, Properties handlerSnippets) throws IOException {
        CharListLDT stringLDT = services.getTypeConverter().getCharListLDT();
        SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();
        IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();

        h.addDeclarationsAndAxioms(handlerSnippets);

        h.addKnownSymbol("sort_string");

        handlers.addAll(Arrays.asList(
                H.startsWith(stringLDT),
                H.endsWith(stringLDT),
                H.indexOf(stringLDT),
                H.indexOfChar(stringLDT),
                H.replace(stringLDT),
                H.substring(seqLDT),
                H.length(seqLDT),
                H.concat(seqLDT),
                H.literals(seqLDT),
                H.charAt(seqLDT, intLDT, services)));

        // List of other unimplemented operators:
        // clLastIndexOfChar, clLastIndexOfCl: no direct smtlib equivalent and no string reversal
        // clContains: no usage in String.key
        // compareTo, copyValueOf: Maybe works already, could perhaps be more efficient
        // clTranslateInt, clRemoveZeros, clHashCode, isEmpty: ignore for now
    }

    private Optional<H> findHandler(Term term) {
        return handlers.stream().filter(h -> h.canHandle(term)).findFirst();
    }

    @Override
    public Capability canHandle(Term term) {
        if (!findHandler(term).isPresent()) {
            return Capability.UNABLE;
        }
        return Capability.YES_THIS_INSTANCE;
    }

    @Override
    public boolean canHandle(Operator op) {
        // MasterHandler only uses Capability canHandle(Term term).
        // Given that we provide that, this one remains unimplemented.
        // (I believe the defaults in SMTHandler should be the other way around,
        // given that the boolean return value one is less general).
        return false;
    }

    @Override
    public SExpr handle(MasterHandler h, Term term) throws SMTTranslationException {
        return findHandler(term).get().handle(h, term);
    }
}
