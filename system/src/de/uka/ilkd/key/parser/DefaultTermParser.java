// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser;


import java.io.Reader;

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
            KeYParser parser
                = new KeYParser(ParserMode.TERM, new KeYLexer(
		                in,
		                services.getExceptionHandler()), 
		                "",
				new Recoder2KeY ((Services)services, nss),
                                (Services) services, 
                                nss, 
                                scm);
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

}
