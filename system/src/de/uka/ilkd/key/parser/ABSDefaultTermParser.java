package de.uka.ilkd.key.parser;

import java.io.Reader;
import java.io.StringReader;

import antlr.RecognitionException;
import antlr.TokenStreamException;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.parser.ABSKeYLexer;
import de.uka.ilkd.keyabs.parser.ABSKeYParser;

public class ABSDefaultTermParser implements TermParser {

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.parser.TermParser#parse(java.io.Reader, de.uka.ilkd.key.logic.sort.Sort, de.uka.ilkd.key.java.IServices, de.uka.ilkd.key.logic.Namespace, de.uka.ilkd.key.logic.Namespace, de.uka.ilkd.key.logic.Namespace, de.uka.ilkd.key.logic.Namespace, de.uka.ilkd.key.pp.AbbrevMap)
     */    
    @Override
    public Term parse(Reader in, 
                      Sort sort, 
                      IServices services,
                      Namespace<ParsableVariable> var_ns,
                      Namespace<SortedOperator> func_ns, 
                      Namespace<Sort> sort_ns,
                      Namespace<IProgramVariable> progVar_ns, 
                      AbbrevMap scm)
        throws ParserException
    {
        return parse(in , sort, services,
                     new NamespaceSet(var_ns,
                                      func_ns, 
                                      sort_ns, 
                                      new Namespace<RuleSet>(),
                                      new Namespace<Choice>(),
                                      progVar_ns),                   
                     scm);
    }


    /* (non-Javadoc)
     * @see de.uka.ilkd.key.parser.TermParser#parse(java.io.Reader, de.uka.ilkd.key.logic.sort.Sort, de.uka.ilkd.key.java.IServices, de.uka.ilkd.key.logic.NamespaceSet, de.uka.ilkd.key.pp.AbbrevMap)
     */    
    @Override
    public Term parse(Reader in, 
                      Sort sort, 
                      IServices services,
                      NamespaceSet nss, 
                      AbbrevMap scm)
        throws ParserException
    {
        try{
            ABSKeYParser parser
                = new ABSKeYParser(ParserMode.TERM, new ABSKeYLexer(
                                in,
                                services.getExceptionHandler()), 
                                "",
                                null,
                                (ABSServices) services, 
                                nss);
            return parser.term();
        } catch (RecognitionException re) {
            throw new ParserException(re.getMessage(),
                                      new Location(re.getFilename(),
                                                   re.getLine(),
                                                   re.getColumn()));
        } catch (TokenStreamException tse) {
            throw new ParserException(tse.getMessage(), null);
        }
    }


	@Override
	public IdDeclaration parseId(StringReader stringReader, IServices services, NamespaceSet nss, AbbrevMap scm) 
	        throws ParserException {
        ABSKeYParser parser =
                new ABSKeYParser (ParserMode.DECLARATION, new ABSKeYLexer ( stringReader,
                                 services.getExceptionHandler() ), "",
                                 (ABSServices) services,
                                 nss );
        try {
			return parser.id_declaration();
		} catch (RecognitionException re) {
            throw new ParserException(re.getMessage(),
                    new Location(re.getFilename(),
                                 re.getLine(),
                                 re.getColumn()));
		} catch (TokenStreamException tse) {
            throw new ParserException(tse.getMessage(), null);
		}
	}


}
