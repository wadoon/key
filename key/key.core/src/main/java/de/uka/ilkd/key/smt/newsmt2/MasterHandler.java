package de.uka.ilkd.key.smt.newsmt2;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.ServiceLoader;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class MasterHandler {

    private final Services services;
    /** Exceptions that occur during translation */
    private List<Throwable> exceptions = new ArrayList<>();

    /** The different handlers */
    private List<SMTHandler> handlers = new ArrayList<>();

    /** All declarations */
    private List<Writable> declarations = new ArrayList<>();

    /** All axioms */
    private List<Writable> axioms = new ArrayList<>();

    /** All SMT options */
    private List<Writable> options = new ArrayList<>();

    /** A list of known symbols */
    private Set<String> knownSymbols  = new HashSet<>();

    /** A list of untranslatable values*/
    private Map<Term, SExpr> unknownValues  = new HashMap<>();

    /** Properties files */
    private Properties snippets = new Properties();

    /** A set of sorts occurring in a problem */
    private HashSet<Sort> sorts = new HashSet<>();

    /** Global state, i.e. a counter for the number of distinct field variables */
    private Map<String, Object> translationState = new HashMap<>();

    public MasterHandler(Services services) throws IOException {

        this.services = services;

        snippets.loadFromXML(getClass().getResourceAsStream("preamble.xml"));

        for (SMTHandler smtHandler : ServiceLoader.load(SMTHandler.class)) {
            smtHandler.init(this, services);
            registerSnippets(smtHandler.getClass());
            handlers.add(smtHandler);
        }


        // If there are options in the preamble pass them through verbatim.
        if (snippets.containsKey("opts")) {
            VerbatimSMT opts = new VerbatimSMT(snippets.getProperty("opts"));
            addOption(opts);
        }

        // sort the entries in the snippets to make this deterministic
        SortedSet<Object> keys = new TreeSet<>(snippets.keySet());
        for (Object k : keys) {
            String key = k.toString();
            if(key.endsWith(".auto")) {
                // strip the ".auto" and add the snippet
                addFromSnippets(key.substring(0, key.length() - 5));
            }
        }

    }

    public SExpr translate(Term problem) {
        try {
            for (SMTHandler smtHandler : handlers) {
                if(smtHandler.canHandle(problem)) {
                    return smtHandler.handle(this, problem);
                }
            }
            return handleAsUnknownValue(problem);
        } catch(Exception ex) {
            exceptions.add(ex);
            return handleAsUnknownValue(problem);
        }
    }

    public SExpr translate(Term problem, Type type)  {
        try {
            return SExprs.coerce(translate(problem), type);
        }  catch(Exception ex) {
            exceptions.add(ex);
            try {
                return SExprs.coerce(handleAsUnknownValue(problem), type);
            } catch (SMTTranslationException e) {
                // This can actually never happen since a universe element is translated
                throw new Error(e);
            }
        }
    }

    /**
     * If no handler can handle a term, it is taken care of here.
     * @param problem the problematic term
     * @return a generic translation as unknown value
     */
    private SExpr handleAsUnknownValue(Term problem) {
        if (unknownValues.containsKey(problem)) {
            return unknownValues.get(problem);
        }
        int number = unknownValues.size();
        SExpr abbr = new SExpr("unknown_" + number, Type.UNIVERSE);
        SExpr e = new SExpr("declare-const", Type.UNIVERSE, abbr.toString(), "U");
        addAxiom(e);
        unknownValues.put(problem, abbr);
        return abbr;
    }

    /**
     * Treats the given term as a function call.
     * @param functionName the name of the function
     * @param term the term to be translated
     * @return an expression with the name functionName and subterms as children
     */
    SExpr handleAsFunctionCall(String functionName, Term term) {
        return handleAsFunctionCall(functionName, Type.UNIVERSE, term);
    }

    /**
     * Treats the given term as a function call.
     * @param functionName the name of the function
     * @param term the term to be translated
     * @return an expression with the name functionName and subterms as children
     */
    SExpr handleAsFunctionCall(String functionName, Type type, Term term) {
        addFromSnippets(functionName);
        List<SExpr> children = new ArrayList<>();
        for (int i = 0; i < term.arity(); i++) {
            children.add(translate(term.sub(i), Type.UNIVERSE));
        }
        return new SExpr(functionName, type, children);
    }

    /**
     * Decides whether a symbol is already known to the master handler.
     * @param pr the string to test
     * @return true iff the name is already known
     */
    boolean isKnownSymbol(String pr) {
        return knownSymbols.contains(pr);
    }

    void addKnownSymbol(String symbol) {
        knownSymbols.add(symbol);
    }

    public List<Throwable> getExceptions() {
        return exceptions;
    }

    public List<SExpr> translate(Iterable<Term> terms, Type type) throws SMTTranslationException {
        return SExprs.coerce(translate(terms), type);
    }

    public List<SExpr> translate(Iterable<Term> terms) {
        List<SExpr> result = new LinkedList<>();
        for (Term term : terms) {
            result.add(translate(term));
        }
        return result;
    }

    public List<Writable> getDeclarations() {
        return declarations;
    }

    void addDeclaration(Writable decl) {
        declarations.add(decl);
    }

    void addAxiom(Writable decl) {
        axioms.add(decl);
    }

    public List<Writable> getAxioms() {
        return axioms;
    }

    public void addSort(Sort s) {
        sorts.add(s);
    }

    public HashSet<Sort> getSorts() {
        return sorts;
    }

    public Map<Term, SExpr> getUnknownValues() {
        return unknownValues;
    }

    public List<Writable> getOptions() {
        return options;
    }

    public void addOption(Writable w) {
        options.add(w);
    }

    void addFromSnippets(String functionName) {
        if (isKnownSymbol(functionName)) {
            return;
        }

        // mark it known to avoid cyclic inclusion
        addKnownSymbol(functionName);

        if (snippets.containsKey(functionName + ".decls")) {
            VerbatimSMT decl = new VerbatimSMT(snippets.getProperty(functionName + ".decls"));
            addDeclaration(decl);
        }

        if (snippets.containsKey(functionName + ".axioms")) {
            VerbatimSMT ax = new VerbatimSMT(snippets.getProperty(functionName + ".axioms"));
            addAxiom(ax);
        }

        String[] deps = snippets.getProperty(functionName + ".deps", "").trim().split(", *");
        for (String dep : deps) {
            addFromSnippets(dep);
        }
    }

    Map<String, Object> getTranslationState() {
        return translationState;
    }

    /**
     * @deprecated Use SExprs.coerce
     */
    @Deprecated
    public SExpr coerce(SExpr sExpr, Type type) throws SMTTranslationException {
        return SExprs.coerce(sExpr, type);
    }

    public void registerSnippets(Class<?> aClass) throws IOException {
        String resourceName = aClass.getSimpleName() + ".preamble.xml";
        URL resource = aClass.getResource(resourceName);
        if (resource != null) {
            registerSnippets(resource);
        }
    }

    private void registerSnippets(URL resource) throws IOException {
        try (InputStream is = resource.openStream()) {
            snippets.loadFromXML(is);
        }
    }

    public void registerSnippets(Properties props) {
        snippets.putAll(props);
    }

    public String getSnippet(String s) {
        return snippets.getProperty(s);
    }

    public String getSnippet(String s, String orElse) {
        return snippets.getProperty(s, orElse);
    }

    public Writable getSnippet(String s, Writable orElse) {
        String result = snippets.getProperty(s);
        if (result == null) {
            return orElse;
        } else {
            return new VerbatimSMT(result);
        }
    }

    public boolean hasSnippet(String s) {
        return snippets.containsKey(s);
    }
}