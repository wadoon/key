package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

import java.io.IOException;
import java.util.*;

public class StringHandler implements SMTHandler {

    public static final Type STRING = new Type("String", "s2u", "u2s");

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

        private static O strContent() {
            return new O(CharListLDT.STRINGCONTENT_NAME, translatedSubs ->
                translatedSubs.get(0));
        }

        private static O startsWith(CharListLDT stringLDT) {
            return new O(stringLDT.getClStartsWith(), translatedSubs ->
                new SExpr("str.prefixof", Type.BOOL, translatedSubs));
        }

        private static O endsWith(CharListLDT stringLDT) {
            return new O(stringLDT.getClEndsWith(), translatedSubs ->
                new SExpr("str.suffixof", Type.BOOL, translatedSubs));
        }

        private static O indexOf(CharListLDT stringLDT) {
            return new O(stringLDT.getClIndexOfCl(), translatedSubs -> {
                SExpr startPos = translatedSubs.get(1);
                translatedSubs.set(1, translatedSubs.get(2));
                translatedSubs.set(2, startPos);
                return new SExpr("str.indexof", IntegerOpHandler.INT, translatedSubs);
            });
        }

        private static O length(SeqLDT seqLDT) {
            return new O(seqLDT.getSeqLen(), translatedSubs ->
                new SExpr("str.len", IntegerOpHandler.INT, translatedSubs));
        }

        private static O concat(SeqLDT seqLDT) {
            return new O(seqLDT.getSeqConcat(), translatedSubs ->
                new SExpr("str.++", STRING, translatedSubs));
        }

        private static O equals() {
            return new O(Equality.EQUALS, translatedSubs ->
                new SExpr("=", Type.BOOL, translatedSubs));
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

    private static class H {
        private O op;
        private Type type;
        private List<H> subHandlers;

        private H(O op, Type type, List<H> subHandlers) {
            this.op = op;
            this.type = type;
            this.subHandlers = subHandlers;
        }

        private static H inner(O op, H... subHandlers) {
            return new H(op, null, Arrays.asList(subHandlers));
        }

        private static H leaf(Type type) {
            return new H(null, type, null);
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
                    H.leaf(IntegerOpHandler.INT),
                    H.inner(O.strContent(), H.leaf(STRING)));
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

        private boolean isLeaf() {
            return op == null;
        }

        private boolean canHandle(Term t) {
            if (isLeaf()) {
                return true;
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
                return h.translate(term, type);
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
                H.length(seqLDT),
                H.concat(seqLDT)));

        // List of other unimplemented operators:
        // clReplace, clIndexOfChar: needs char -> String embedding
        // clLastIndexOfChar, clLastIndexOfCl: no direct smtlib equivalent and no string reversal
        // clContains: no usage in String.key
        // clTranslateInt, clRemoveZeros, clHashCode: ignore for now
        // String.get: needs String -> char conversion
        // String.concat: strContent(result) = ... encoding
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
