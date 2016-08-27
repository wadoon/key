// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.parser;


import java.io.Reader;
import java.io.StringReader;

import antlr.RecognitionException;
import antlr.TokenStreamException;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
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


/** This class wraps the default KeY-Term-Parser.
 *
 * @author Hubert Schmid
 */

public final class DefaultTermParser implements TermParser {

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


    /** The method reads the input and parses a term with the
     * specified namespaces. The method ensures, that the term has the
     * specified sort.
     * @param sort The expected sort of the term; must not be null.
     * @return The parsed term of the specified sort.
     * @throws ParserException The method throws a ParserException, if
     * the input could not be parsed correctly or the term has an
     * invalid sort. */    
    public Term parse(Reader in,
	    	      Sort sort, 
	    	      IServices services,
                      NamespaceSet nss, 
                      AbbrevMap scm)
        throws ParserException
    {
        try{
            KeYParser parser
                = new KeYParser(ParserMode.TERM, new KeYLexer(
		                in,
		                services.getExceptionHandler()), 
		                "",
				new Recoder2KeY ((Services)services, nss),
                                (Services) services, 
                                nss, 
                                scm);

	    final Term result = parser.term();
	    if (sort != null &&  ! result.sort().extendsTrans(sort))
	        throw new ParserException("Expected sort "+sort+", but parser returns sort "+result.sort()+".", null);
        return result;
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
        KeYParser parser =
                new KeYParser (ParserMode.DECLARATION, new KeYLexer ( stringReader,
                                 services.getExceptionHandler() ), "",
                                 (Services) services,
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
