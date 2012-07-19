package de.uka.ilkd.key.parser;

import java.io.Reader;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.AbbrevMap;

public interface TermParser {

    /** The method reads the input and parses a term with the
     * specified namespaces. The method ensures, that the term has the
     * specified sort.
     * @param sort The expected sort of the term.
     * @return The parsed term of the specified sort.
     * @throws ParserException The method throws a ParserException, if
     * the input could not be parsed correctly or the term has an
     * invalid sort. */
    public abstract Term parse(Reader in, Sort sort, IServices services,
            Namespace var_ns, Namespace func_ns, Namespace sort_ns,
            Namespace progVar_ns, AbbrevMap scm) throws ParserException;

    /** The method reads the input and parses a term with the
     * specified namespaces. The method ensures, that the term has the
     * specified sort.
     * @param sort The expected sort of the term.
     * @return The parsed term of the specified sort.
     * @throws ParserException The method throws a ParserException, if
     * the input could not be parsed correctly or the term has an
     * invalid sort. */
    public abstract Term parse(Reader in, Sort sort, IServices services,
            NamespaceSet nss, AbbrevMap scm) throws ParserException;

}