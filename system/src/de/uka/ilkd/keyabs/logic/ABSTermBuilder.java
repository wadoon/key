package de.uka.ilkd.keyabs.logic;

import java.io.StringReader;

import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.parser.ABSDefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.keyabs.abs.ABSServices;

public class ABSTermBuilder extends TermBuilder<ABSServices> {

    public static ABSTermBuilder TB = new ABSTermBuilder();

    private ABSTermBuilder() {}

    @Override
    public Term parseTerm(String s, IServices services) throws ParserException {
        return parseTerm(s, services, services.getNamespaces());
    }

    @Override
    public Term parseTerm(String s, IServices services, NamespaceSet namespaces)
            throws ParserException {
        AbbrevMap abbr = (services.getProof() == null)
                ? null : services.getProof().abbreviations();
        Term term = new ABSDefaultTermParser().parse(
                new StringReader(s), null, services, namespaces, abbr);
        return term;
    }

    public Term wellFormed(LocationVariable heap, ABSServices services) {
        return func(services.getTypeConverter().getHeapLDT().getWellFormed(heap.sort()), var(heap));
    }

    public Term wellFormedHistory(LocationVariable history, ABSServices services) {
        return func(services.getTypeConverter().getHistoryLDT().getWellFormed(), var(history));
    }

    public Term classInvariant(LocationVariable history, LocationVariable heap, IProgramVariable thisRef, ABSServices services) {
        return func(services.getCInv(), var(history), var(heap), var(thisRef));
    }

    public Term classInvariant(LocationVariable history, LocationVariable heap, Function thisRef, ABSServices services) {
        return func(services.getCInv(), var(history), var(heap), func(thisRef));
    }

}