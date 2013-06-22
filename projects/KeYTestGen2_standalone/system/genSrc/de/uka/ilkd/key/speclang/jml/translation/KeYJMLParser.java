// $ANTLR 2.7.7 (2006-11-01): "jmlparser.g" -> "KeYJMLParser.java"$

    package de.uka.ilkd.key.speclang.jml.translation;

    import java.io.StringReader;

    import de.uka.ilkd.key.collection.*;
    import de.uka.ilkd.key.java.JavaInfo;
    import de.uka.ilkd.key.java.Position;
    import de.uka.ilkd.key.java.Services;
    import de.uka.ilkd.key.java.abstraction.*;
    import de.uka.ilkd.key.java.expression.literal.StringLiteral;
    import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
    import de.uka.ilkd.key.ldt.*;
    import de.uka.ilkd.key.logic.*;
    import de.uka.ilkd.key.logic.op.*;
    import de.uka.ilkd.key.logic.sort.*;
    import de.uka.ilkd.key.parser.ParserException;
    import de.uka.ilkd.key.proof.OpReplacer;
    import de.uka.ilkd.key.speclang.PositionedString;
    import de.uka.ilkd.key.speclang.translation.*;
    import de.uka.ilkd.key.util.Pair;
    import de.uka.ilkd.key.util.Triple; 

    import java.math.BigInteger;
    import java.util.List;
    import java.util.Map;
    import java.util.LinkedHashMap;

import antlr.TokenBuffer;
import antlr.TokenStreamException;
import antlr.TokenStreamIOException;
import antlr.ANTLRException;
import antlr.LLkParser;
import antlr.Token;
import antlr.TokenStream;
import antlr.RecognitionException;
import antlr.NoViableAltException;
import antlr.MismatchedTokenException;
import antlr.SemanticException;
import antlr.ParserSharedInputState;
import antlr.collections.impl.BitSet;

public class KeYJMLParser extends antlr.LLkParser       implements KeYJMLParserTokenTypes
 {

    private static final TermBuilder TB = TermBuilder.DF;

    private Services services;
    private JavaInfo javaInfo;
    private KeYJavaType containerType;
    private IntegerLDT intLDT;
    private HeapLDT heapLDT;
    private LocSetLDT locSetLDT;
    private BooleanLDT booleanLDT;
    private SLTranslationExceptionManager excManager;
    private List<PositionedString> warnings = new java.util.ArrayList<PositionedString>();

    private JMLTranslator translator;

    private ProgramVariable selfVar;
    private ImmutableList<ProgramVariable> paramVars;
    private ProgramVariable resultVar;
    private ProgramVariable excVar;
    private Map<LocationVariable,Term> atPres;
    
    // Helper objects
    private JMLResolverManager resolverManager;
    private JavaIntegerSemanticsHelper intHelper;

    
    public KeYJMLParser(TokenStream lexer,
		String fileName,
		Position offsetPos,
		Services services,
		KeYJavaType specInClass,
		ProgramVariable self,
		ImmutableList<ProgramVariable> paramVars,
		ProgramVariable result,
		ProgramVariable exc,
		Map<LocationVariable,Term> atPres) {
	this(lexer);

	// save parameters
	this.services       = services;
	this.javaInfo       = services.getJavaInfo();
	containerType  =   specInClass;
	this.intLDT         = services.getTypeConverter().getIntegerLDT();
	this.heapLDT        = services.getTypeConverter().getHeapLDT();
	this.locSetLDT      = services.getTypeConverter().getLocSetLDT();
	this.booleanLDT     = services.getTypeConverter().getBooleanLDT();
	this.excManager     = new SLTranslationExceptionManager(this,
				    				fileName, 
				    				offsetPos);
        this.translator     = new JMLTranslator(excManager, services);
	
	this.selfVar	    = self;
	this.paramVars      = paramVars;
	this.resultVar      = result;
	this.excVar	    = exc;
	this.atPres         = atPres;

        intHelper = new JavaIntegerSemanticsHelper(services, excManager);
	// initialize helper objects
	this.resolverManager = new JMLResolverManager(this.javaInfo,
						      specInClass,
						      selfVar,
						      this.excManager);

	// initialize namespaces
	resolverManager.pushLocalVariablesNamespace();
	if(paramVars != null) {
	    resolverManager.putIntoTopLocalVariablesNamespace(paramVars);
	}
	if(resultVar != null) {
	    resolverManager.putIntoTopLocalVariablesNamespace(resultVar);
	}
    }
    
    
    public KeYJMLParser(PositionedString ps,
		Services services,
		KeYJavaType specInClass,
		ProgramVariable self,
		ImmutableList<ProgramVariable> paramVars,
		ProgramVariable result,
		ProgramVariable exc,
		Map<LocationVariable,Term> atPres) {
	this(new KeYJMLLexer(new StringReader(ps.text)), 
	     ps.fileName, 
	     ps.pos,
	     services,
	     specInClass,
	     self,
	     paramVars,
	     result,
	     exc,
	     atPres);
    }


    public SLTranslationExceptionManager getExceptionManager() {
        return excManager;
    }


    private void raiseError(String msg) throws SLTranslationException {
	throw excManager.createException(msg);
    }    
    
    private void raiseError(String msg, Token t) throws SLTranslationException {
	throw excManager.createException(msg, t);
    }
    
    private void raiseError(String msg, Token t, Exception cause) throws SLTranslationException {
        throw excManager.createException(msg, t, cause);
    }
    
    private void raiseNotSupported(String feature) 
	    throws SLTranslationException {
	throw excManager.createWarningException(feature + " not supported"); 
    }
    
    /**
     * This is used for features without semantics such as labels or annotations.
     * @author bruns
     * @since 1.7.2178
     */
    private void addIgnoreWarning(String feature, Token t) {
        String msg = feature + " is not supported and has been silently ignored.";
        warnings.add(new PositionedString(msg,t));
    }
    
    public List<PositionedString> getWarnings(){
        // mutable -- but who cares?
        return warnings;
    }
	

    public Term parseExpression() throws SLTranslationException {
	Term result = null;

	try {
	    result = expression().getTerm();
	} catch (antlr.ANTLRException e) {
	    throw excManager.convertException(e);
	}

	return TB.convertToFormula(result, services);
    }


    public ImmutableList<ProgramVariable> parseVariableDeclaration() throws SLTranslationException {

	Pair<KeYJavaType,ImmutableList<LogicVariable>> vars;
	try {
	    vars = quantifiedvardecls();
	} catch (antlr.ANTLRException e) {
	    throw excManager.convertException(e);
	}

	ImmutableList<ProgramVariable> result = ImmutableSLList.<ProgramVariable>nil();
	for(LogicVariable lv : vars.second) {
	    ProgramVariable pv 
	    	= new LocationVariable(new ProgramElementName(
	    	                           lv.name().toString()), 
	                               vars.first);
	    result = result.append(pv);
	}
	return result;
    }



    /**
     * Extracts a term's subterms as an array.
     */
    private Term[] getSubTerms(Term term) {
	Term[] result = new Term[term.arity()];
	for(int i = 0; i < term.arity(); i++) {
	    result[i] = term.sub(i);
	    assert result[i] != null;
	}
	return result;
    }


    /**
     * Extracts the sorts from an array of terms as an array.
     */
    private Sort[] getSorts(Term[] terms) {
	Sort[] result = new Sort[terms.length];
	for(int i = 0; i < terms.length; i++) {
	    result[i] = terms[i].sort();
	}
	return result;
    }

	private LocationVariable getBaseHeap() {
		return services.getTypeConverter().getHeapLDT().getHeap();
	}

	private LocationVariable getSavedHeap() {
		return services.getTypeConverter().getHeapLDT().getSavedHeap();
	}

    /**
     * Converts a term so that all of its non-rigid operators refer to the pre-state.
     */
    // TODO: remove when all clients have been moved to JMLTranslator
    private Term convertToOld(final Term term) {
	    assert atPres != null && atPres.get(getBaseHeap()) != null;
	    Map<Term, Term> map = new LinkedHashMap<Term, Term>();
        for (LocationVariable heap : atPres.keySet()) {
            Term heapAtPre = atPres.get(heap);
            if (heapAtPre != null) {
                map.put(TB.var(heap), heapAtPre);
            }
        }
	    OpReplacer or = new OpReplacer(map);
	    return or.replace(term);
    }

    private Term convertToBackup(Term term) {
	assert atPres != null && atPres.get(getSavedHeap()) != null;
	Map map = new LinkedHashMap();
	map.put(TB.var(getBaseHeap()), TB.var(getSavedHeap()));
        if(atPres.get(getBaseHeap()) != null) {
	  map.put(atPres.get(getBaseHeap()), atPres.get(getSavedHeap()));
        }
	OpReplacer or = new OpReplacer(map);
	return or.replace(term);
    }


    private String createSignatureString(ImmutableList<SLExpression> signature) {
	if (signature == null || signature.isEmpty()) {
	    return "";
	}
	String sigString = "";
	
	for(SLExpression expr : signature) {
	    sigString += expr.getType().getFullName() + ", ";
	}
	
	return sigString.substring(0, sigString.length() - 2);
    }
    
    
    private SLExpression lookupIdentifier(String lookupName,
					  SLExpression receiver,
					  SLParameters params,
					  Token t)
				       throws SLTranslationException {

	// Identifier with suffix in parantheses? Probably a method call
	// parse in the parameter list and call again
	try {
	    if (LA(1) == LPAREN) {
	    	return receiver;
	    }
	} catch (TokenStreamException e) {
            raiseError("internal Error: no further Token in Stream");
	}

	SLExpression result = null;
	try {
	 result = resolverManager.resolve(receiver,
	   			      lookupName,
				      params);
	} catch(SLTranslationException exc) {
	   // no type name found maybe package?
	}
	
	if(result != null) {
	    return result;
	}
    
	// no identifier found, maybe it was just a package prefix.
	// but package prefixes don't have a receiver!
	// Let primarysuffix handle faulty method call.
	if (receiver != null && params == null) {
	    raiseError("Identifier " + lookupName + " not found: " + 
	               lookupName);
	}
	
	return null;
    }

protected KeYJMLParser(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
}

public KeYJMLParser(TokenBuffer tokenBuf) {
  this(tokenBuf,2);
}

protected KeYJMLParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
}

public KeYJMLParser(TokenStream lexer) {
  this(lexer,2);
}

public KeYJMLParser(ParserSharedInputState state) {
  super(state,2);
  tokenNames = _tokenNames;
}

	public final Object  top() throws RecognitionException, TokenStreamException, SLTranslationException {
		Object result = null;
		
		
		{
		switch ( LA(1)) {
		case ACCESSIBLE:
		{
			result=accessibleclause();
			break;
		}
		case ASSIGNABLE:
		{
			result=assignableclause();
			break;
		}
		case BREAKS:
		{
			result=breaksclause();
			break;
		}
		case CONTINUES:
		{
			result=continuesclause();
			break;
		}
		case DEPENDS:
		{
			result=dependsclause();
			break;
		}
		case DECLASSIFY:
		{
			result=declassifyclause();
			break;
		}
		case ENSURES:
		{
			result=ensuresclause();
			break;
		}
		case REPRESENTS:
		{
			result=representsclause();
			break;
		}
		case REQUIRES:
		{
			result=requiresclause();
			break;
		}
		case RESPECTS:
		{
			result=respectsclause();
			break;
		}
		case RETURNS:
		{
			result=returnsclause();
			break;
		}
		case SIGNALS:
		{
			result=signalsclause();
			break;
		}
		case SIGNALS_ONLY:
		{
			result=signalsonlyclause();
			break;
		}
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case BITWISENOT:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case MINUS:
		case NONNULLELEMENTS:
		case NOT:
		case NOT_MODIFIED:
		case OLD:
		case PLUS:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			result=termexpression();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case SEMI:
		{
			match(SEMI);
			break;
		}
		case EOF:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(Token.EOF_TYPE);
		return result;
	}
	
	public final Term  accessibleclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		Token  acc = null;
		
		acc = LT(1);
		match(ACCESSIBLE);
		result=storeRefUnion();
		if ( inputState.guessing==0 ) {
			result = translator.translate(acc.getText(), Term.class, result, services);
		}
		return result;
	}
	
	public final Term  assignableclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		Token  ass = null;
		
		ass = LT(1);
		match(ASSIGNABLE);
		{
		switch ( LA(1)) {
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case BITWISENOT:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case EVERYTHING:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case MINUS:
		case NONNULLELEMENTS:
		case NOT:
		case NOT_MODIFIED:
		case NOT_SPECIFIED:
		case NOTHING:
		case OLD:
		case PLUS:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			result=storeRefUnion();
			if ( inputState.guessing==0 ) {
				result = translator.translate(ass.getText(), Term.class, result, services);
			}
			break;
		}
		case LESS_THAN_NOTHING:
		{
			match(LESS_THAN_NOTHING);
			if ( inputState.guessing==0 ) {
				result = TB.strictlyNothing();
			}
			break;
		}
		case STRICTLY_NOTHING:
		{
			match(STRICTLY_NOTHING);
			if ( inputState.guessing==0 ) {
				result = TB.strictlyNothing();
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final Pair  breaksclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Pair result=null;
		
		Token  breaks = null;
		Token  id = null;
		
		String label = null;
		Term pred = null;
		
		
		breaks = LT(1);
		match(BREAKS);
		match(LPAREN);
		{
		switch ( LA(1)) {
		case IDENT:
		{
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				label = id.getText();
			}
			break;
		}
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(RPAREN);
		{
		switch ( LA(1)) {
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case BITWISENOT:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case MINUS:
		case NONNULLELEMENTS:
		case NOT:
		case NOT_MODIFIED:
		case NOT_SPECIFIED:
		case OLD:
		case PLUS:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SAME:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			pred=predornot();
			break;
		}
		case EOF:
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			result = translator.translate(breaks.getText(), Pair.class, pred, label, services);
				
		}
		return result;
	}
	
	public final Pair  continuesclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Pair result=null;
		
		Token  continues = null;
		Token  id = null;
		
		String label = null;
		Term pred = null;
		
		
		continues = LT(1);
		match(CONTINUES);
		match(LPAREN);
		{
		switch ( LA(1)) {
		case IDENT:
		{
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				label = id.getText();
			}
			break;
		}
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(RPAREN);
		{
		switch ( LA(1)) {
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case BITWISENOT:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case MINUS:
		case NONNULLELEMENTS:
		case NOT:
		case NOT_MODIFIED:
		case NOT_SPECIFIED:
		case OLD:
		case PLUS:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SAME:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			pred=predornot();
			break;
		}
		case EOF:
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			result = translator.translate(continues.getText(), Pair.class, pred, label, services);
				
		}
		return result;
	}
	
	public final Triple<ObserverFunction,Term,Term>  dependsclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Triple<ObserverFunction,Term,Term> result=null;
		
		Token  dep = null;
		
		SLExpression lhs, mby = null;
		Term rhs;
		
		
		dep = LT(1);
		match(DEPENDS);
		lhs=expression();
		match(COLON);
		rhs=storeRefUnion();
		{
		switch ( LA(1)) {
		case MEASURED_BY:
		{
			match(MEASURED_BY);
			mby=expression();
			break;
		}
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(SEMI);
		if ( inputState.guessing==0 ) {
			result = translator.translate(
			dep.getText(), Triple.class, lhs, rhs, mby, services);
		}
		return result;
	}
	
	public final ImmutableList<Term>  declassifyclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<Term> result = ImmutableSLList.<Term>nil();
		
		Token  del = null;
		
		Term declass = null;
		Term frompart = null;
		Term topart = null;
		Term ifpart = null;
		
		
		del = LT(1);
		match(DECLASSIFY);
		declass=predicate();
		{
		switch ( LA(1)) {
		case FROM:
		{
			match(FROM);
			frompart=storeRefUnion();
			break;
		}
		case EOF:
		case SEMI:
		case TO:
		case IF:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case TO:
		{
			match(TO);
			topart=storeRefUnion();
			break;
		}
		case EOF:
		case SEMI:
		case IF:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		{
		switch ( LA(1)) {
		case IF:
		{
			match(IF);
			ifpart=predicate();
			break;
		}
		case EOF:
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			result = translator.translate(del.getText(), ImmutableList.class, declass, frompart, topart, ifpart, services);
		}
		return result;
	}
	
	public final Term  ensuresclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		Token  ens = null;
		
		ens = LT(1);
		match(ENSURES);
		result=termexpression();
		if ( inputState.guessing==0 ) {
			result = translator.translate(ens.getText(), Term.class, result, services);
		}
		return result;
	}
	
	public final Pair<ObserverFunction,Term>  representsclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Pair<ObserverFunction,Term> result=null;
		
		Token  rep = null;
		
		SLExpression lhs, rhs;
		Term t = null;
		
		
		rep = LT(1);
		match(REPRESENTS);
		lhs=expression();
		if ( inputState.guessing==0 ) {
			
			// TODO: move code out of the parser!
			if(!lhs.isTerm()
			|| !(lhs.getTerm().op() instanceof ObserverFunction)
			|| lhs.getTerm().sub(0).op() != heapLDT.getHeap()) {
			raiseError("Represents clause with unexpected lhs: " + lhs);
			} else if(selfVar != null
			&& ((ObserverFunction)lhs.getTerm().op()).isStatic()) {
			raiseError("Represents clauses for static model fields must be static.");
			}
			
		}
		{
		if (((LA(1)==EQUAL_SINGLE||LA(1)==LARROW) && (_tokenSet_0.member(LA(2))))&&( // TODO: move code out of the parser!
          !lhs.getTerm().sort().equals(locSetLDT.targetSort()))) {
			{
			{
			switch ( LA(1)) {
			case LARROW:
			{
				match(LARROW);
				break;
			}
			case EQUAL_SINGLE:
			{
				match(EQUAL_SINGLE);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			rhs=expression();
			if ( inputState.guessing==0 ) {
				// TODO: move code out of the parser!
				if(!rhs.isTerm()) {
				raiseError("Represents clause with unexpected rhs: " + rhs);
				}
				Term rhsTerm = rhs.getTerm();
				if(rhsTerm.sort() == Sort.FORMULA) {
				rhsTerm = TB.ife(rhsTerm, TB.TRUE(services), TB.FALSE(services));
				}
				t = TB.equals(lhs.getTerm(), rhsTerm);
				
			}
			}
		}
		else if (((LA(1)==EQUAL_SINGLE||LA(1)==LARROW) && (_tokenSet_1.member(LA(2))))&&( // TODO: move code out of the parser!
          lhs.getTerm().sort().equals(locSetLDT.targetSort()))) {
			{
			{
			switch ( LA(1)) {
			case LARROW:
			{
				match(LARROW);
				break;
			}
			case EQUAL_SINGLE:
			{
				match(EQUAL_SINGLE);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			t=storeRefUnion();
			if ( inputState.guessing==0 ) {
				// TODO: move code out of the parser!
				t = TB.equals(lhs.getTerm(), t);
				
			}
			}
		}
		else if ((LA(1)==SUCH_THAT)) {
			{
			match(SUCH_THAT);
			t=predicate();
			}
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		if ( inputState.guessing==0 ) {
			result = translator.translate(rep.getText(), Pair.class, lhs, t, services);
		}
		return result;
	}
	
	public final Term  requiresclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		Token  req = null;
		
		req = LT(1);
		match(REQUIRES);
		result=termexpression();
		if ( inputState.guessing==0 ) {
			result = translator.translate(req.getText(), Term.class, result, services);
		}
		return result;
	}
	
	public final ImmutableList<Term>  respectsclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<Term> result = ImmutableSLList.<Term>nil();
		
		Token  resp = null;
		
		Term term = null;
		
		
		resp = LT(1);
		match(RESPECTS);
		term=storeref();
		if ( inputState.guessing==0 ) {
			result = result.append(term);
		}
		{
		_loop24:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				term=storeref();
				if ( inputState.guessing==0 ) {
					result = result.append(term);
				}
			}
			else {
				break _loop24;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			result = translator.translate(resp.getText(), ImmutableList.class, result, services);
		}
		return result;
	}
	
	public final Term  returnsclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result=null;
		
		Token  rtrns = null;
		
		Term pred = null;
		
		
		rtrns = LT(1);
		match(RETURNS);
		{
		switch ( LA(1)) {
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case BITWISENOT:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case MINUS:
		case NONNULLELEMENTS:
		case NOT:
		case NOT_MODIFIED:
		case NOT_SPECIFIED:
		case OLD:
		case PLUS:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SAME:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			result=predornot();
			break;
		}
		case EOF:
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			result = translator.translate(rtrns.getText(), Term.class, result, services);
				
		}
		return result;
	}
	
	public final Term  signalsclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result=null;
		
		Token  sig = null;
		Token  id = null;
		
		KeYJavaType excType = null;
		Term pred = null;
		String vName = null;
		LogicVariable eVar = null;
		
		
		sig = LT(1);
		match(SIGNALS);
		match(LPAREN);
		excType=referencetype();
		{
		switch ( LA(1)) {
		case IDENT:
		{
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				vName = id.getText();
			}
			break;
		}
		case RPAREN:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(RPAREN);
		if ( inputState.guessing==0 ) {
			
				    if (vName != null) {
					eVar = new LogicVariable(new Name(vName), excType.getSort());
					resolverManager.pushLocalVariablesNamespace();
					resolverManager.putIntoTopLocalVariablesNamespace(eVar, excType);
				    }
				
		}
		{
		switch ( LA(1)) {
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case BITWISENOT:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case MINUS:
		case NONNULLELEMENTS:
		case NOT:
		case NOT_MODIFIED:
		case NOT_SPECIFIED:
		case OLD:
		case PLUS:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SAME:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			result=predornot();
			break;
		}
		case EOF:
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    if (vName != null) {
					resolverManager.popLocalVariablesNamespace();
				    }
			result = translator.translate(sig.getText(), Term.class, result, eVar, excVar, excType, services);
				
		}
		return result;
	}
	
	public final Term  signalsonlyclause() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		Token  sigo = null;
		
		ImmutableList<KeYJavaType> typeList = ImmutableSLList.<KeYJavaType>nil();
		KeYJavaType type = null;
		
		
		sigo = LT(1);
		match(SIGNALS_ONLY);
		{
		switch ( LA(1)) {
		case NOTHING:
		{
			match(NOTHING);
			break;
		}
		case IDENT:
		{
			type=referencetype();
			if ( inputState.guessing==0 ) {
				typeList = typeList.append(type);
			}
			{
			_loop31:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					type=referencetype();
					if ( inputState.guessing==0 ) {
						typeList = typeList.append(type);
					}
				}
				else {
					break _loop31;
				}
				
			} while (true);
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			result = translator.translate(sigo.getText(), Term.class, typeList, this.excVar, services);
		}
		return result;
	}
	
	public final Term  termexpression() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		
		SLExpression exp = null;
		
		
		exp=expression();
		if ( inputState.guessing==0 ) {
			result = (Term) exp.getTerm();
		}
		return result;
	}
	
	public final Term  storeRefUnion() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		
		ImmutableList<Term> list = null;
		
		
		list=storeRefList();
		if ( inputState.guessing==0 ) {
			result = TB.union(services, list);
		}
		return result;
	}
	
	public final Term  predicate() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result=null;
		
		
		SLExpression expr;
		
		
		expr=expression();
		if ( inputState.guessing==0 ) {
			
				    if(!expr.isTerm() && expr.getTerm().sort() == Sort.FORMULA) {
				        raiseError("Expected a formula: " + expr);
				    } 
				    result = expr.getTerm();
				
		}
		return result;
	}
	
	public final SLExpression  expression() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		result=assignmentexpr();
		if ( inputState.guessing==0 ) {
			
				    if(!result.isTerm()) {
				        raiseError("Expected a term: " + result);
				    }
				
		}
		return result;
	}
	
	public final Term  storeref() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		
		SLExpression expr;
		
		
		switch ( LA(1)) {
		case NOTHING:
		{
			match(NOTHING);
			if ( inputState.guessing==0 ) {
				result = TB.empty(services);
			}
			break;
		}
		case EVERYTHING:
		{
			match(EVERYTHING);
			if ( inputState.guessing==0 ) {
				result = TB.createdLocs(services);
			}
			break;
		}
		case NOT_SPECIFIED:
		{
			match(NOT_SPECIFIED);
			if ( inputState.guessing==0 ) {
				result = TB.createdLocs(services);
			}
			break;
		}
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case BITWISENOT:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case MINUS:
		case NONNULLELEMENTS:
		case NOT:
		case NOT_MODIFIED:
		case OLD:
		case PLUS:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			result=storeRefExpr();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return result;
	}
	
	public final KeYJavaType  referencetype() throws RecognitionException, TokenStreamException, SLTranslationException {
		KeYJavaType type = null;
		
		
		String typename;
		
		
		typename=name();
		if ( inputState.guessing==0 ) {
			
				    try {
					type = resolverManager.resolve(null, typename, null).getType();
				    } catch (NullPointerException e) {
					raiseError("Type " + typename + " not found.");
				    }
				
		}
		return type;
	}
	
	public final Term  predornot() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result=null;
		
		
		switch ( LA(1)) {
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case BITWISENOT:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case MINUS:
		case NONNULLELEMENTS:
		case NOT:
		case NOT_MODIFIED:
		case OLD:
		case PLUS:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			result=predicate();
			break;
		}
		case NOT_SPECIFIED:
		{
			match(NOT_SPECIFIED);
			break;
		}
		case SAME:
		{
			match(SAME);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return result;
	}
	
	public final ImmutableList<Term>  storeRefList() throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<Term> result = ImmutableSLList.<Term>nil();
		
		
		Term t = null;
		
		
		t=storeref();
		if ( inputState.guessing==0 ) {
			result = result.append(t);
		}
		{
		_loop44:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				t=storeref();
				if ( inputState.guessing==0 ) {
					result = result.append(t);
				}
			}
			else {
				break _loop44;
			}
			
		} while (true);
		}
		return result;
	}
	
	public final Term  storeRefIntersect() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		
		ImmutableList<Term> list = null;
		
		
		list=storeRefList();
		if ( inputState.guessing==0 ) {
			result = TB.intersect(services, list);
		}
		return result;
	}
	
	public final Term  storeRefExpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		
		SLExpression expr;
		
		
		expr=expression();
		if ( inputState.guessing==0 ) {
			
			result = translator.translate("store_ref_expr", Term.class, expr, services);
			
		}
		return result;
	}
	
	public final Term  createLocset() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		
		ImmutableList<SLExpression> list;
		
		
		{
		switch ( LA(1)) {
		case LOCSET:
		{
			match(LOCSET);
			break;
		}
		case SINGLETON:
		{
			match(SINGLETON);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(LPAREN);
		list=exprList();
		match(RPAREN);
		if ( inputState.guessing==0 ) {
			
			result = translator.translate("create locset", Term.class, list, services);
			
		}
		return result;
	}
	
	public final ImmutableList<SLExpression>  exprList() throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<SLExpression> result = ImmutableSLList.<SLExpression>nil();
		
		
		SLExpression expr = null;
		
		
		expr=expression();
		if ( inputState.guessing==0 ) {
			result = result.append(expr);
		}
		{
		_loop51:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				expr=expression();
				if ( inputState.guessing==0 ) {
					result = result.append(expr);
				}
			}
			else {
				break _loop51;
			}
			
		} while (true);
		}
		return result;
	}
	
	public final SLExpression  specarrayrefexpr(
		SLExpression receiver, String fullyQualifiedName, Token lbrack
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result = null;
		
		
		SLExpression rangeFrom=null;
		SLExpression rangeTo=null;
		
		
		{
		switch ( LA(1)) {
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case BITWISENOT:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case MINUS:
		case NONNULLELEMENTS:
		case NOT:
		case NOT_MODIFIED:
		case OLD:
		case PLUS:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			{
			rangeFrom=expression();
			{
			switch ( LA(1)) {
			case DOTDOT:
			{
				match(DOTDOT);
				rangeTo=expression();
				break;
			}
			case RBRACKET:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			}
			break;
		}
		case MULT:
		{
			match(MULT);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			result = translator.translate("array reference", SLExpression.class, services, receiver, fullyQualifiedName, lbrack, rangeFrom, rangeTo);
			
		}
		return result;
	}
	
	public final SLExpression  assignmentexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		result=conditionalexpr();
		return result;
	}
	
	public final SLExpression  conditionalexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		SLExpression a,b;
		
		
		result=equivalenceexpr();
		{
		switch ( LA(1)) {
		case QUESTIONMARK:
		{
			match(QUESTIONMARK);
			a=conditionalexpr();
			match(COLON);
			b=conditionalexpr();
			if ( inputState.guessing==0 ) {
				
					    	result = translator.translate(JMLTranslator.JMLKeyWord.CONDITIONAL, services, result, a, b);
					
			}
			break;
		}
		case EOF:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case LARROW:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  equivalenceexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  eq = null;
		
		SLExpression right = null;
		
		
		result=impliesexpr();
		{
		switch ( LA(1)) {
		case EQV_ANTIV:
		{
			eq = LT(1);
			match(EQV_ANTIV);
			right=equivalenceexpr();
			if ( inputState.guessing==0 ) {
				result = translator.translate(eq.getText(), SLExpression.class, result, right, services);
			}
			break;
		}
		case EOF:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case LARROW:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  impliesexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		SLExpression expr;
		
		
		result=logicalorexpr();
		{
		switch ( LA(1)) {
		case IMPLIES:
		{
			match(IMPLIES);
			expr=impliesnonbackwardexpr();
			if ( inputState.guessing==0 ) {
				
						result = new SLExpression(TB.imp(TB.convertToFormula(result.getTerm(), services),
						                                 TB.convertToFormula(expr.getTerm(), services)));
					
			}
			break;
		}
		case IMPLIESBACKWARD:
		{
			{
			int _cnt68=0;
			_loop68:
			do {
				if ((LA(1)==IMPLIESBACKWARD)) {
					match(IMPLIESBACKWARD);
					expr=logicalorexpr();
					if ( inputState.guessing==0 ) {
						
								    result = new SLExpression(TB.imp(TB.convertToFormula(expr.getTerm(), services),
								                                     TB.convertToFormula(result.getTerm(), services)));
								
					}
				}
				else {
					if ( _cnt68>=1 ) { break _loop68; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt68++;
			} while (true);
			}
			break;
		}
		case EOF:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case LARROW:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case EQV_ANTIV:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  logicalorexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		SLExpression expr;
		
		
		result=logicalandexpr();
		{
		switch ( LA(1)) {
		case LOGICALOR:
		{
			match(LOGICALOR);
			expr=logicalorexpr();
			if ( inputState.guessing==0 ) {
				
						result = new SLExpression(TB.or(TB.convertToFormula(result.getTerm(), services),
						                                TB.convertToFormula(expr.getTerm(), services)));
					
			}
			break;
		}
		case EOF:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case IMPLIES:
		case IMPLIESBACKWARD:
		case LARROW:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case EQV_ANTIV:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  impliesnonbackwardexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		SLExpression expr;
		
		
		result=logicalorexpr();
		{
		switch ( LA(1)) {
		case IMPLIES:
		{
			match(IMPLIES);
			expr=impliesnonbackwardexpr();
			if ( inputState.guessing==0 ) {
				
						result = new SLExpression(TB.imp(TB.convertToFormula(result.getTerm(), services),
						                                 TB.convertToFormula(expr.getTerm(), services)));
					
			}
			break;
		}
		case EOF:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case LARROW:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case EQV_ANTIV:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  logicalandexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		SLExpression expr;
		
		
		result=inclusiveorexpr();
		{
		switch ( LA(1)) {
		case LOGICALAND:
		{
			match(LOGICALAND);
			expr=logicalandexpr();
			if ( inputState.guessing==0 ) {
				
						result = new SLExpression(TB.and(TB.convertToFormula(result.getTerm(), services),
						                                 TB.convertToFormula(expr.getTerm(), services)));
					
			}
			break;
		}
		case EOF:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case IMPLIES:
		case IMPLIESBACKWARD:
		case LARROW:
		case LOGICALOR:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case EQV_ANTIV:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  inclusiveorexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		SLExpression expr;
		
		
		result=exclusiveorexpr();
		{
		switch ( LA(1)) {
		case INCLUSIVEOR:
		{
			match(INCLUSIVEOR);
			expr=inclusiveorexpr();
			if ( inputState.guessing==0 ) {
				
					       if(intHelper.isIntegerTerm(result)) {
				result = intHelper.buildPromotedOrExpression(result,expr);
				} else {
				result = new SLExpression(TB.or(TB.convertToFormula(result.getTerm(), services),
				TB.convertToFormula(expr.getTerm(), services)));
				}
					
			}
			break;
		}
		case EOF:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case IMPLIES:
		case IMPLIESBACKWARD:
		case LARROW:
		case LOGICALAND:
		case LOGICALOR:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case EQV_ANTIV:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  exclusiveorexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		SLExpression expr;
		
		
		result=andexpr();
		{
		switch ( LA(1)) {
		case XOR:
		{
			match(XOR);
			expr=exclusiveorexpr();
			if ( inputState.guessing==0 ) {
				
					       if(intHelper.isIntegerTerm(result)) {
				result = intHelper.buildPromotedXorExpression(result,expr);
				} else {
				Term resultFormula = TB.convertToFormula(result.getTerm(), services);
				Term exprFormula = TB.convertToFormula(expr.getTerm(), services);
				result = new SLExpression(TB.or(TB.and(resultFormula, TB.not(exprFormula)), 
				TB.and(TB.not(resultFormula), exprFormula)));
				}
					
			}
			break;
		}
		case EOF:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case IMPLIES:
		case IMPLIESBACKWARD:
		case INCLUSIVEOR:
		case LARROW:
		case LOGICALAND:
		case LOGICALOR:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case EQV_ANTIV:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  andexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		SLExpression expr;
		
		
		result=equalityexpr();
		if ( inputState.guessing==0 ) {
			
				    if(!result.isTerm()) {
					raiseError("Found a type where only a term is allowed: " 
						   + result);
				    }
				
		}
		{
		switch ( LA(1)) {
		case AND:
		{
			match(AND);
			expr=andexpr();
			if ( inputState.guessing==0 ) {
				
					       if(intHelper.isIntegerTerm(result)) {
				result = intHelper.buildPromotedAndExpression(result, expr);
				} else {
				result = new SLExpression(TB.and(TB.convertToFormula(result.getTerm(), services),
				TB.convertToFormula(expr.getTerm(), services)));
				}
					
			}
			break;
		}
		case EOF:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case IMPLIES:
		case IMPLIESBACKWARD:
		case INCLUSIVEOR:
		case LARROW:
		case LOGICALAND:
		case LOGICALOR:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case XOR:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case EQV_ANTIV:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  equalityexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  eq = null;
		
			SLExpression right = null;
		
		
		result=relationalexpr();
		{
		switch ( LA(1)) {
		case EQ_NEQ:
		{
			eq = LT(1);
			match(EQ_NEQ);
			right=equalityexpr();
			if ( inputState.guessing==0 ) {
				result = translator.translate(eq.getText(), SLExpression.class, result, right, services);
			}
			break;
		}
		case EOF:
		case AND:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case IMPLIES:
		case IMPLIESBACKWARD:
		case INCLUSIVEOR:
		case LARROW:
		case LOGICALAND:
		case LOGICALOR:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case XOR:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case EQV_ANTIV:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  relationalexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  lt = null;
		Token  gt = null;
		Token  leq = null;
		Token  geq = null;
		Token  io = null;
		Token  st = null;
		
		Function f = null;
		KeYJavaType type = null;
		SLExpression right = null;
		Token opToken = null;
		
		
		result=shiftexpr();
		{
		switch ( LA(1)) {
		case LT:
		{
			lt = LT(1);
			match(LT);
			right=shiftexpr();
			if ( inputState.guessing==0 ) {
				
						f = intLDT.getLessThan();
						opToken = lt;
					
			}
			break;
		}
		case GT:
		{
			gt = LT(1);
			match(GT);
			right=shiftexpr();
			if ( inputState.guessing==0 ) {
				
						f = intLDT.getGreaterThan();
						opToken = gt;
					
			}
			break;
		}
		case LEQ:
		{
			leq = LT(1);
			match(LEQ);
			right=shiftexpr();
			if ( inputState.guessing==0 ) {
				
						f = intLDT.getLessOrEquals();
						opToken = leq;
					
			}
			break;
		}
		case GEQ:
		{
			geq = LT(1);
			match(GEQ);
			right=shiftexpr();
			if ( inputState.guessing==0 ) {
				
						f = intLDT.getGreaterOrEquals();
						opToken = geq;
					
			}
			break;
		}
		case INSTANCEOF:
		{
			io = LT(1);
			match(INSTANCEOF);
			type=typespec();
			if ( inputState.guessing==0 ) {
				
						f = type.getSort().getInstanceofSymbol(services);
						opToken = io;
					
			}
			break;
		}
		case ST:
		{
			st = LT(1);
			match(ST);
			right=shiftexpr();
			if ( inputState.guessing==0 ) {
				
						if (result.isTerm() || right.isTerm()) {
						    raiseError("Cannot build subtype expression from terms.", st);
						}
						assert result.isType();
						assert right.isType();
						
						if (result.getTerm() == null) {
						    raiseError("subtype expression <: only supported for" +
							" \\typeof() arguments on the left side.", st);
						}
						
						Sort os = right.getType().getSort();
						Function ioFunc = os.getInstanceofSymbol(services);
						
						result = new SLExpression(
						    TB.equals(
							TB.func(ioFunc, result.getTerm()),
							TB.TRUE(services)));
					
			}
			break;
		}
		case EOF:
		case AND:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case IMPLIES:
		case IMPLIESBACKWARD:
		case INCLUSIVEOR:
		case LARROW:
		case LOGICALAND:
		case LOGICALOR:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case XOR:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case EQV_ANTIV:
		case EQ_NEQ:
		case RPAREN:
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				    if (f != null) {
					assert opToken != null;
					if (result.isType()) {
					    raiseError("Cannot build relational expression from type " +
						result.getType().getName() + ".", opToken);
					}
					assert result.isTerm();
					
					try {
						if (right == null) {
						    // instanceof-expression
						    result = new SLExpression(
							TB.and(TB.not(TB.equals(result.getTerm(), TB.NULL(services))),
							       TB.equals(TB.func(f, result.getTerm()), TB.TRUE(services))));
						} else {
						    if (right.isType()) {
						    raiseError("Cannot build relational expression from type " +
							right.getType().getName() + ".", opToken);
						    }
						    assert right.isTerm();
						    
						    result = new SLExpression(
							TB.func(f,result.getTerm(),right.getTerm()));
						}
					} catch (TermCreationException e) {
					    raiseError("Error in relational expression: " + e.getMessage());
					} catch (IllegalArgumentException e) {
					    raiseError("Internal error.");
					}
				    }
				
		}
		return result;
	}
	
	public final SLExpression  shiftexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  sr = null;
		Token  sl = null;
		Token  usr = null;
		
		SLExpression e;
		
		
		result=additiveexpr();
		{
		_loop87:
		do {
			switch ( LA(1)) {
			case SHIFTRIGHT:
			{
				sr = LT(1);
				match(SHIFTRIGHT);
				e=additiveexpr();
				if ( inputState.guessing==0 ) {
					
					result = translator.<SLExpression>translate(sr.getText(), SLExpression.class, services, result, e);
						
				}
				break;
			}
			case SHIFTLEFT:
			{
				sl = LT(1);
				match(SHIFTLEFT);
				e=additiveexpr();
				if ( inputState.guessing==0 ) {
					
					result = translator.<SLExpression>translate(sl.getText(), SLExpression.class, services, result, e);
						
				}
				break;
			}
			case UNSIGNEDSHIFTRIGHT:
			{
				usr = LT(1);
				match(UNSIGNEDSHIFTRIGHT);
				e=additiveexpr();
				if ( inputState.guessing==0 ) {
					
					result = translator.<SLExpression>translate(usr.getText(), SLExpression.class, services, result, e);
						
				}
				break;
			}
			default:
			{
				break _loop87;
			}
			}
		} while (true);
		}
		return result;
	}
	
	public final KeYJavaType  typespec() throws RecognitionException, TokenStreamException, SLTranslationException {
		KeYJavaType t = null;
		
		
		int dim = 0;
		
		
		t=type();
		{
		switch ( LA(1)) {
		case LBRACKET:
		{
			dim=dims();
			if ( inputState.guessing==0 ) {
				
						String fullName = t.getFullName();
						for (int i=0; i < dim; i++) {
						    fullName += "[]";
						}
						t = javaInfo.getKeYJavaType(fullName);
					if(t == null && dim > 0) {
					    //try to create missing array type
					      try {
					    javaInfo.readJavaBlock("{" + fullName + " k;}");
					    t = javaInfo.getKeYJavaType(fullName);
					    } catch (Exception e) {
					    t = null;
						}
					    }
					
			}
			break;
		}
		case EOF:
		case AND:
		case COLON:
		case COMMA:
		case DOTDOT:
		case EQUAL_SINGLE:
		case IMPLIES:
		case IMPLIESBACKWARD:
		case INCLUSIVEOR:
		case LARROW:
		case LOGICALAND:
		case LOGICALOR:
		case QUESTIONMARK:
		case RBRACE:
		case SEMI:
		case SUCH_THAT:
		case XOR:
		case MEASURED_BY:
		case FROM:
		case TO:
		case IF:
		case EQV_ANTIV:
		case EQ_NEQ:
		case RPAREN:
		case RBRACKET:
		case IDENT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return t;
	}
	
	public final SLExpression  additiveexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  plus = null;
		Token  minus = null;
		
		SLExpression e;
		
		
		result=multexpr();
		{
		_loop90:
		do {
			switch ( LA(1)) {
			case PLUS:
			{
				plus = LT(1);
				match(PLUS);
				e=multexpr();
				if ( inputState.guessing==0 ) {
					
					result = translator.<SLExpression>translate(plus.getText(), SLExpression.class, services, result, e);
						
				}
				break;
			}
			case MINUS:
			{
				minus = LT(1);
				match(MINUS);
				e=multexpr();
				if ( inputState.guessing==0 ) {
					
						    result = translator.<SLExpression>translate(minus.getText(), SLExpression.class, services, result, e);
						
				}
				break;
			}
			default:
			{
				break _loop90;
			}
			}
		} while (true);
		}
		return result;
	}
	
	public final SLExpression  multexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		SLExpression e;
		
		
		result=unaryexpr();
		{
		_loop93:
		do {
			switch ( LA(1)) {
			case MULT:
			{
				match(MULT);
				e=unaryexpr();
				if ( inputState.guessing==0 ) {
					
						    if (result.isType()) {
							raiseError("Cannot build multiplicative expression from type " +
							    result.getType().getName() + ".");
						    }
						    if (e.isType()) {
							raiseError("Cannot multiply by type " +
							    e.getType().getName() + ".");
						    }
						    assert result.isTerm();
						    assert e.isTerm();
						
						    result = intHelper.buildMulExpression(result, e);
						
				}
				break;
			}
			case DIV:
			{
				match(DIV);
				e=unaryexpr();
				if ( inputState.guessing==0 ) {
					
						    if (result.isType()) {
							raiseError("Cannot build multiplicative expression from type " +
							    result.getType().getName() + ".");
						    }
						    if (e.isType()) {
							raiseError("Cannot divide by type " +
							    e.getType().getName() + ".");
						    }
						    assert result.isTerm();
						    assert e.isTerm();
					
						    result = intHelper.buildDivExpression(result, e);
						
				}
				break;
			}
			case MOD:
			{
				match(MOD);
				e=unaryexpr();
				if ( inputState.guessing==0 ) {
					
						    if (result.isType()) {
							raiseError("Cannot build multiplicative expression from type " +
							    result.getType().getName() + ".");
						    }
						    if (e.isType()) {
							raiseError("Cannot build modulo expression from type " +
							    e.getType().getName() + ".");
						    }
						    assert result.isTerm();
						    assert e.isTerm();
					
						    result = intHelper.buildModExpression(result, e);
						
				}
				break;
			}
			default:
			{
				break _loop93;
			}
			}
		} while (true);
		}
		return result;
	}
	
	public final SLExpression  unaryexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		switch ( LA(1)) {
		case PLUS:
		{
			match(PLUS);
			result=unaryexpr();
			if ( inputState.guessing==0 ) {
				
					    if (result.isType()) {
						raiseError("Cannot build  +" + result.getType().getName() + ".");
					    }
					    assert result.isTerm();
					    
					    result = intHelper.buildPromotedUnaryPlusExpression(result);
					
			}
			break;
		}
		case MINUS:
		{
			match(MINUS);
			result=unaryexpr();
			if ( inputState.guessing==0 ) {
				
					    if (result.isType()) {
						raiseError("Cannot build  -" + result.getType().getName() + ".");
					    }
					    assert result.isTerm();
				
					    result = intHelper.buildUnaryMinusExpression(result);
					
			}
			break;
		}
		default:
			boolean synPredMatched96 = false;
			if (((LA(1)==LPAREN) && (_tokenSet_2.member(LA(2))))) {
				int _m96 = mark();
				synPredMatched96 = true;
				inputState.guessing++;
				try {
					{
					match(LPAREN);
					typespec();
					match(RPAREN);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched96 = false;
				}
				rewind(_m96);
inputState.guessing--;
			}
			if ( synPredMatched96 ) {
				result=castexpr();
			}
			else if ((_tokenSet_3.member(LA(1))) && (_tokenSet_4.member(LA(2)))) {
				result=unaryexprnotplusminus();
			}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return result;
	}
	
	public final SLExpression  castexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result = null;
		
		
		KeYJavaType type = null;
		
		
		match(LPAREN);
		type=typespec();
		match(RPAREN);
		result=unaryexpr();
		if ( inputState.guessing==0 ) {
			
			result = translator.translate(JMLTranslator.JMLKeyWord.CAST, services, intHelper, type, result);
			
		}
		return result;
	}
	
	public final SLExpression  unaryexprnotplusminus() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		SLExpression e;
		
		
		switch ( LA(1)) {
		case NOT:
		{
			match(NOT);
			e=unaryexpr();
			if ( inputState.guessing==0 ) {
				
					    if (e.isType()) {
						raiseError("Cannot negate type " + e.getType().getName() + ".");
					    }
					    
					    Term t = e.getTerm();
					    assert t != null;
					    
					    if (t.sort() == Sort.FORMULA) {
						result = new SLExpression(TB.not(t));
					    } else if(t.sort() == booleanLDT.targetSort()) {
						result = new SLExpression(TB.not(TB.equals(t, TB.TRUE(services))));
					    } else {
						raiseError("Wrong type in not-expression: " + t);
					    }
					
			}
			break;
		}
		case BITWISENOT:
		{
			match(BITWISENOT);
			e=unaryexpr();
			if ( inputState.guessing==0 ) {
				
					    if(e.isType()) {
						raiseError("Cannot negate type " + e.getType().getName() + ".");
					    }
						
					    result = intHelper.buildPromotedNegExpression(e);
					
			}
			break;
		}
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case NONNULLELEMENTS:
		case NOT_MODIFIED:
		case OLD:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			result=postfixexpr();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return result;
	}
	
	public final SLExpression  postfixexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		String fullyQualifiedName = "";
		SLExpression expr = null;
		
		
		expr=primaryexpr();
		if ( inputState.guessing==0 ) {
			
				    fullyQualifiedName = LT(0).getText();
				
		}
		{
		_loop101:
		do {
			if ((LA(1)==DOT||LA(1)==LPAREN||LA(1)==LBRACKET)) {
				if ( inputState.guessing==0 ) {
					
						        if (expr != null && expr.getType() == null) {
						            raiseError("SLExpression without a type: " + expr);
						        }/* else if (expr != null && expr.getType().getJavaType() instanceof PrimitiveType) {
							    raiseError("Cannot build postfix expression from primitive type.");
							}*/	    		
						
				}
				expr=primarysuffix(expr, fullyQualifiedName);
				if ( inputState.guessing==0 ) {
						    
							fullyQualifiedName += "." + LT(0).getText();
						
				}
			}
			else {
				break _loop101;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    if (expr == null) {
					raiseError("Expression " + fullyQualifiedName + " cannot be resolved.");
				    }
				    result = expr; //.getTerm();
				
		}
		return result;
	}
	
	public final SLExpression  primaryexpr() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  id = null;
		Token  inv = null;
		
		Term s1, s2;
		
		
		switch ( LA(1)) {
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		{
			result=constant();
			break;
		}
		case IDENT:
		{
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				result = lookupIdentifier(id.getText(), null, null, id);
			}
			break;
		}
		case INV:
		{
			inv = LT(1);
			match(INV);
			if ( inputState.guessing==0 ) {
				result = translator.translate(inv.getText(),services,
				selfVar==null? null: TB.var(selfVar),containerType);
			}
			break;
		}
		case TRUE:
		{
			match(TRUE);
			if ( inputState.guessing==0 ) {
				result = new SLExpression(TB.tt());
			}
			break;
		}
		case FALSE:
		{
			match(FALSE);
			if ( inputState.guessing==0 ) {
				result = new SLExpression(TB.ff());
			}
			break;
		}
		case NULL:
		{
			match(NULL);
			if ( inputState.guessing==0 ) {
				result = new SLExpression(TB.NULL(services));
			}
			break;
		}
		case BACKUP:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LOCKSET:
		case NONNULLELEMENTS:
		case NOT_MODIFIED:
		case OLD:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			result=jmlprimary();
			break;
		}
		case THIS:
		{
			match(THIS);
			if ( inputState.guessing==0 ) {
				
				if(selfVar == null) {
					raiseError("Cannot access \"this\" in a static context!"); 
				}
				result = new SLExpression(TB.var(selfVar), selfVar.getKeYJavaType());
				
			}
			break;
		}
		case NEW:
		{
			new_expr();
			break;
		}
		case LBRACE:
		{
			array_initializer();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return result;
	}
	
	public final SLExpression  primarysuffix(
		SLExpression receiver, String fullyQualifiedName
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  id = null;
		Token  l = null;
		Token  lbrack = null;
		
		String lookupName = null;   
		ImmutableList<SLExpression> params = ImmutableSLList.<SLExpression>nil();
		
		
		if ( inputState.guessing==0 ) {
			
			lookupName = fullyQualifiedName;
			
		}
		{
		switch ( LA(1)) {
		case LPAREN:
		{
			if ( inputState.guessing==0 ) {
				
					    if(receiver != null) {
						lookupName = LT(0).getText();
					    }
					
			}
			l = LT(1);
			match(LPAREN);
			{
			switch ( LA(1)) {
			case FALSE:
			case NEW:
			case NULL:
			case THIS:
			case TRUE:
			case BACKUP:
			case BITWISENOT:
			case CREATED:
			case DURATION:
			case ELEMTYPE:
			case FRESH:
			case INDEX:
			case INV:
			case INVARIANT_FOR:
			case IS_INITIALIZED:
			case LBRACE:
			case LOCKSET:
			case MINUS:
			case NONNULLELEMENTS:
			case NOT:
			case NOT_MODIFIED:
			case OLD:
			case PLUS:
			case PRE:
			case REACH:
			case REACHLOCS:
			case RESULT:
			case SPACE:
			case STRING_EQUAL:
			case TRANSACTIONUPDATED:
			case TYPEOF:
			case TYPE_SMALL:
			case VALUES:
			case WORKINGSPACE:
			case LOCSET:
			case EMPTYSET:
			case SINGLETON:
			case UNION:
			case INTERSECT:
			case SETMINUS:
			case ALLFIELDS:
			case ALLOBJECTS:
			case UNIONINF:
			case DISJOINT:
			case SUBSET:
			case NEWELEMSFRESH:
			case SEQGET:
			case SEQEMPTY:
			case SEQSINGLETON:
			case SEQCONCAT:
			case SEQSUB:
			case SEQREVERSE:
			case SEQREPLACE:
			case INDEXOF:
			case DL_ESCAPE:
			case LPAREN:
			case IDENT:
			case HEXNUMERAL:
			case DIGITS:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case INFORMAL_DESCRIPTION:
			case UNION_2:
			{
				params=expressionlist();
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    result = lookupIdentifier(lookupName, receiver, new SLParameters(params), l);
					    if (result == null) {
						raiseError("Method " + lookupName + "("
						           + createSignatureString(params) + ") not found!", l);
					    }
					
			}
			break;
		}
		case LBRACKET:
		{
			lbrack = LT(1);
			match(LBRACKET);
			result=specarrayrefexpr(receiver, fullyQualifiedName, lbrack);
			match(RBRACKET);
			break;
		}
		default:
			if ((LA(1)==DOT) && (LA(2)==IDENT)) {
				match(DOT);
				id = LT(1);
				match(IDENT);
				if ( inputState.guessing==0 ) {
					
						    if(receiver == null) {
							// Receiver was only a package/classname prefix
							lookupName = fullyQualifiedName + "." + id.getText();
						    } else {
							lookupName = id.getText();
						    }
						    try {
						    	result = lookupIdentifier(lookupName, receiver, null, id);
						    } catch(SLTranslationException e) {
						    	result = lookupIdentifier(fullyQualifiedName + "." + lookupName, null, null, id);
						    }
						
				}
			}
			else if ((LA(1)==DOT) && (LA(2)==THIS)) {
				match(DOT);
				match(THIS);
				if ( inputState.guessing==0 ) {
					
						result = new SLExpression(
							services.getTypeConverter().findThisForSort(receiver.getType().getSort(),
												    TB.var(selfVar), 
												    javaInfo.getKeYJavaType(selfVar.sort()), 
												    true),
					receiver.getType());
					
				}
			}
			else if ((LA(1)==DOT) && (LA(2)==INV)) {
				match(DOT);
				match(INV);
				if ( inputState.guessing==0 ) {
					
					result = translator.translate("\\inv",services,receiver.getTerm(),receiver.getType());
					
				}
			}
			else if ((LA(1)==DOT) && (LA(2)==MULT)) {
				match(DOT);
				match(MULT);
				if ( inputState.guessing==0 ) {
					
						     result = new SLExpression(TB.allFields(services, receiver.getTerm()),
						                               javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
					
				}
			}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return result;
	}
	
	public final SLExpression  constant() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		result=javaliteral();
		return result;
	}
	
	public final SLExpression  jmlprimary() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  desc = null;
		Token  escape = null;
		Token  lblneg = null;
		Token  lblpos = null;
		Token  pd = null;
		Token  tk2 = null;
		Token  tk3 = null;
		Token  tk4 = null;
		
		ImmutableList<SLExpression> list = null;
		ImmutableList<Term> tlist = null;
		SLExpression e1 = null;
		SLExpression e2 = null;
		SLExpression e3 = null;
		KeYJavaType typ;
		Term t, t2 = null;
		Token tk = null;
		Pair<KeYJavaType,ImmutableList<LogicVariable>> declVars = null;    
		
		
		switch ( LA(1)) {
		case RESULT:
		{
			match(RESULT);
			if ( inputState.guessing==0 ) {
				
					    if(resultVar==null) {
						raiseError("\\result used in wrong context");
					    } else
					    result = new SLExpression(TB.var(resultVar), resultVar.getKeYJavaType());
					
			}
			break;
		}
		case OLD:
		case PRE:
		{
			result=oldexpression();
			break;
		}
		case TRANSACTIONUPDATED:
		{
			result=transactionUpdated();
			break;
		}
		case BACKUP:
		{
			match(BACKUP);
			match(LPAREN);
			result=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    if (atPres == null || atPres.get(getSavedHeap()) == null) {
						raiseError("JML construct " +
							   "\\backup not allowed in this context.");
					    }	    
					    typ = result.getType();
					    if(typ != null) {
					      result = new SLExpression(convertToBackup(result.getTerm()), 
					                                result.getType());
					    } else {
					      result = new SLExpression(convertToBackup(result.getTerm()));
					    }
					
			}
			break;
		}
		case CREATED:
		{
			match(CREATED);
			match(LPAREN);
			result=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
						raiseNotSupported("\\created is deliberately not supported in this KeY version, you should not need it");
					
			}
			break;
		}
		case NONNULLELEMENTS:
		{
			match(NONNULLELEMENTS);
			match(LPAREN);
			result=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    t = result.getTerm();
					    Term resTerm = TB.not(TB.equals(t, TB.NULL(services)));
				
					    if (t.sort() instanceof ArraySort) {
						LogicVariable i = new LogicVariable(new Name("i"), javaInfo
								.getKeYJavaType(PrimitiveType.JAVA_INT)
								.getSort());
				
						// See JML reference manual
						// http://www.cs.iastate.edu/~leavens/JML/jmlrefman/jmlrefman_11.html#SEC139		
						Term range = TB.and(
						    TB.leq(TB.zero(services), TB.var(i), services),
						    TB.lt(TB.var(i), TB.dotLength(services, t), services));
						Term body = TB.equals(
						    TB.dotArr(services, t, TB.var(i)),
						    TB.NULL(services));
						body = TB.not(body);
						body = TB.imp(range, body);
				
						result = new SLExpression(TB.and(resTerm, TB.all(i, body)));
					    } else {
					        raiseError("\\nonnullelements may only be applied to arrays");
					    }
					
			}
			break;
		}
		case INFORMAL_DESCRIPTION:
		{
			desc = LT(1);
			match(INFORMAL_DESCRIPTION);
			if ( inputState.guessing==0 ) {
				
					    // was: raiseNotSupported("informal predicates");
					    result = translator.translate("(* *)", SLExpression.class, services, desc, 
					        selfVar, resultVar, paramVars, atPres == null ? null : atPres.get(getBaseHeap()));
					
			}
			break;
		}
		case DL_ESCAPE:
		{
			escape = LT(1);
			match(DL_ESCAPE);
			match(LPAREN);
			{
			switch ( LA(1)) {
			case FALSE:
			case NEW:
			case NULL:
			case THIS:
			case TRUE:
			case BACKUP:
			case BITWISENOT:
			case CREATED:
			case DURATION:
			case ELEMTYPE:
			case FRESH:
			case INDEX:
			case INV:
			case INVARIANT_FOR:
			case IS_INITIALIZED:
			case LBRACE:
			case LOCKSET:
			case MINUS:
			case NONNULLELEMENTS:
			case NOT:
			case NOT_MODIFIED:
			case OLD:
			case PLUS:
			case PRE:
			case REACH:
			case REACHLOCS:
			case RESULT:
			case SPACE:
			case STRING_EQUAL:
			case TRANSACTIONUPDATED:
			case TYPEOF:
			case TYPE_SMALL:
			case VALUES:
			case WORKINGSPACE:
			case LOCSET:
			case EMPTYSET:
			case SINGLETON:
			case UNION:
			case INTERSECT:
			case SETMINUS:
			case ALLFIELDS:
			case ALLOBJECTS:
			case UNIONINF:
			case DISJOINT:
			case SUBSET:
			case NEWELEMSFRESH:
			case SEQGET:
			case SEQEMPTY:
			case SEQSINGLETON:
			case SEQCONCAT:
			case SEQSUB:
			case SEQREVERSE:
			case SEQREPLACE:
			case INDEXOF:
			case DL_ESCAPE:
			case LPAREN:
			case IDENT:
			case HEXNUMERAL:
			case DIGITS:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case INFORMAL_DESCRIPTION:
			case UNION_2:
			{
				list=expressionlist();
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = translator.translate("\\dl_", SLExpression.class, escape, list, services);
				
			}
			break;
		}
		case NOT_MODIFIED:
		{
			match(NOT_MODIFIED);
			match(LPAREN);
			t=storeRefUnion();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = new SLExpression(translator.translate("\\not_modified", Term.class, services, atPres == null ? null : atPres.get(getBaseHeap()), t));
				
			}
			break;
		}
		case FRESH:
		{
			match(FRESH);
			match(LPAREN);
			list=expressionlist();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    if(atPres == null || atPres.get(getBaseHeap()) == null) {
					        raiseError("\\fresh not allowed in this context");
					    }
					    t = TB.tt();
					    final Sort objectSort = services.getJavaInfo().objectSort();
					    for(SLExpression expr: list) {
					        if(!expr.isTerm()) {
					            raiseError("Expected a term, but found: " + expr);
					        } else if(expr.getTerm().sort().extendsTrans(objectSort)) {
					            t = TB.and(t, 
					                       TB.equals(TB.select(services,
					                                           booleanLDT.targetSort(),
					                                           atPres.get(getBaseHeap()),
					                                           expr.getTerm(),
					                                           TB.func(heapLDT.getCreated())),
					                                 TB.FALSE(services)));
					        } else if(expr.getTerm().sort().extendsTrans(locSetLDT.targetSort())) {
					            t = TB.and(t, TB.subset(services, 
					                                    expr.getTerm(), 
					                                    TB.freshLocs(services, atPres.get(getBaseHeap()))));
					        } else {
					            raiseError("Wrong type: " + expr);
					        }
					    }
					    result = new SLExpression(t);
					
			}
			break;
		}
		case REACH:
		{
			match(REACH);
			match(LPAREN);
			t=storeref();
			match(COMMA);
			e1=expression();
			match(COMMA);
			e2=expression();
			{
			switch ( LA(1)) {
			case COMMA:
			{
				match(COMMA);
				e3=expression();
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = translator.translate("reach", SLExpression.class, t, e1, e2, e3, services);
					
			}
			break;
		}
		case REACHLOCS:
		{
			match(REACHLOCS);
			match(LPAREN);
			t=storeref();
			match(COMMA);
			e1=expression();
			{
			switch ( LA(1)) {
			case COMMA:
			{
				match(COMMA);
				e3=expression();
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = translator.translate("reachLocs", SLExpression.class, t, e1, e3, services);
					
			}
			break;
		}
		case DURATION:
		{
			match(DURATION);
			match(LPAREN);
			result=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    raiseNotSupported("\\duration");
					
			}
			break;
		}
		case SPACE:
		{
			match(SPACE);
			match(LPAREN);
			result=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    raiseNotSupported("\\space");
					
			}
			break;
		}
		case WORKINGSPACE:
		{
			match(WORKINGSPACE);
			match(LPAREN);
			result=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    raiseNotSupported("\\working_space");
					
			}
			break;
		}
		case TYPEOF:
		{
			match(TYPEOF);
			match(LPAREN);
			result=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    result = new SLExpression(result.getTerm(),
					                              result.getType(),
					                              false);
					
			}
			break;
		}
		case ELEMTYPE:
		{
			match(ELEMTYPE);
			match(LPAREN);
			result=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    raiseNotSupported("\\elemtype");
					
			}
			break;
		}
		case TYPE_SMALL:
		{
			match(TYPE_SMALL);
			match(LPAREN);
			typ=typespec();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    result = new SLExpression(typ);
					
			}
			break;
		}
		case LOCKSET:
		{
			match(LOCKSET);
			if ( inputState.guessing==0 ) {
				
					    raiseNotSupported("\\lockset");
					
			}
			break;
		}
		case IS_INITIALIZED:
		{
			match(IS_INITIALIZED);
			match(LPAREN);
			typ=referencetype();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    Term resTerm = TB.equals(
						TB.var(
						    javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, 
									  typ)),
						TB.TRUE(services));
					    result = new SLExpression(resTerm);
					
			}
			break;
		}
		case INVARIANT_FOR:
		{
			match(INVARIANT_FOR);
			match(LPAREN);
			result=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    result = translator.translate("\\invariant_for", SLExpression.class, services, result);
					    
					
			}
			break;
		}
		case INDEX:
		{
			match(INDEX);
			if ( inputState.guessing==0 ) {
				result = translator.translate(JMLTranslator.JMLKeyWord.INDEX, services);
			}
			break;
		}
		case VALUES:
		{
			match(VALUES);
			if ( inputState.guessing==0 ) {
				result = translator.translate(JMLTranslator.JMLKeyWord.VALUES, services);
			}
			break;
		}
		case STRING_EQUAL:
		{
			match(STRING_EQUAL);
			match(LPAREN);
			e1=expression();
			match(COMMA);
			e2=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					    Function strContent
					    	= (Function) services.getNamespaces()
					                     .functions()
					                     .lookup(CharListLDT.STRINGCONTENT_NAME);
				if(strContent == null) {
				raiseError("strings used in spec, but string content "
				+ "function not found");
				}
				return new SLExpression(TB.equals(TB.func(strContent, e1.getTerm()), 
				TB.func(strContent, e2.getTerm())));
				
			}
			break;
		}
		case EMPTYSET:
		{
			match(EMPTYSET);
			if ( inputState.guessing==0 ) {
				
				result = translator.translate(JMLTranslator.JMLKeyWord.EMPTY, services, javaInfo);
				
			}
			break;
		}
		case LOCSET:
		case SINGLETON:
		{
			t=createLocset();
			if ( inputState.guessing==0 ) {
				result = new SLExpression(t, javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
			}
			break;
		}
		case UNION:
		case UNION_2:
		{
			{
			switch ( LA(1)) {
			case UNION:
			{
				match(UNION);
				break;
			}
			case UNION_2:
			{
				match(UNION_2);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(LPAREN);
			t=storeRefUnion();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				result = translator.translate(JMLTranslator.JMLKeyWord.UNION, t, javaInfo);
			}
			break;
		}
		case INTERSECT:
		{
			match(INTERSECT);
			match(LPAREN);
			t=storeRefIntersect();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				result = translator.translate(JMLTranslator.JMLKeyWord.INTERSECT, t, javaInfo);
			}
			break;
		}
		case SETMINUS:
		{
			match(SETMINUS);
			match(LPAREN);
			t=storeref();
			match(COMMA);
			t2=storeref();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = new SLExpression(TB.setMinus(services, t, t2),
				javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
				
			}
			break;
		}
		case ALLFIELDS:
		{
			match(ALLFIELDS);
			match(LPAREN);
			e1=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				if(!e1.isTerm() || !e1.getTerm().sort().extendsTrans(services.getJavaInfo().objectSort())) {
				raiseError("Invalid argument to \\allFields: " + e1);
				}
				result = new SLExpression(TB.allFields(services, e1.getTerm()),
				javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
				
			}
			break;
		}
		case ALLOBJECTS:
		{
			match(ALLOBJECTS);
			match(LPAREN);
			t=storeref();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = new SLExpression(TB.allObjects(services, t.sub(1)),
				javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
				
			}
			break;
		}
		case UNIONINF:
		{
			match(UNIONINF);
			match(LPAREN);
			declVars=quantifiedvardecls();
			match(SEMI);
			if ( inputState.guessing==0 ) {
				
				resolverManager.pushLocalVariablesNamespace();
				resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);
				
			}
			{
			boolean synPredMatched143 = false;
			if (((_tokenSet_0.member(LA(1))) && (_tokenSet_5.member(LA(2))))) {
				int _m143 = mark();
				synPredMatched143 = true;
				inputState.guessing++;
				try {
					{
					predicate();
					match(SEMI);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched143 = false;
				}
				rewind(_m143);
inputState.guessing--;
			}
			if ( synPredMatched143 ) {
				t2=predicate();
				match(SEMI);
			}
			else if ((LA(1)==SEMI)) {
				match(SEMI);
			}
			else if ((_tokenSet_1.member(LA(1))) && (_tokenSet_6.member(LA(2)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			t=storeref();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				resolverManager.popLocalVariablesNamespace();
				if(t2 == null) {
				// unguarded version
					          result = new SLExpression(TB.infiniteUnion(services,
				declVars.second.toArray(new QuantifiableVariable[declVars.second.size()]),
				t),
				javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
				} else {
				// guarded version
				result = new SLExpression(TB.guardedInfiniteUnion(services,
				declVars.second.toArray(new QuantifiableVariable[declVars.second.size()]),
				t2, t),
				javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_LOCSET));
				}
				
			}
			break;
		}
		case DISJOINT:
		{
			pd = LT(1);
			match(DISJOINT);
			match(LPAREN);
			tlist=storeRefList();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = translator.translate(pd.getText(), SLExpression.class, tlist, services);
				
			}
			break;
		}
		case SUBSET:
		{
			match(SUBSET);
			match(LPAREN);
			t=storeref();
			match(COMMA);
			t2=storeref();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = new SLExpression(TB.subset(services, t, t2));
				
			}
			break;
		}
		case NEWELEMSFRESH:
		{
			match(NEWELEMSFRESH);
			match(LPAREN);
			t=storeref();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = new SLExpression(TB.subset(services, 
				t, 
				TB.union(services,
				convertToOld(t),
				TB.freshLocs(services, 
					      atPres == null ? null : atPres.get(getBaseHeap())))));
				
				
			}
			break;
		}
		case SEQEMPTY:
		{
			match(SEQEMPTY);
			if ( inputState.guessing==0 ) {
				
				result = new SLExpression(TB.seqEmpty(services));
				
			}
			break;
		}
		case SEQSINGLETON:
		{
			match(SEQSINGLETON);
			match(LPAREN);
			e1=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = new SLExpression(TB.seqSingleton(services, e1.getTerm()));
				
			}
			break;
		}
		case SEQSUB:
		{
			match(SEQSUB);
			match(LPAREN);
			e1=expression();
			match(COMMA);
			e2=expression();
			match(COMMA);
			e3=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = new SLExpression(TB.seqSub(services, e1.getTerm(), e2.getTerm(), e3.getTerm()));
				
			}
			break;
		}
		case SEQREVERSE:
		{
			match(SEQREVERSE);
			match(LPAREN);
			e1=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = new SLExpression(TB.seqReverse(services, e1.getTerm()));
				
			}
			break;
		}
		case SEQREPLACE:
		{
			match(SEQREPLACE);
			match(LPAREN);
			e1=expression();
			match(COMMA);
			e2=expression();
			match(COMMA);
			e3=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				// short for "e1[0..e2-1]+e3+e1[e2+1..e1.length-1]"
				final Term minusOne = TB.zTerm(services, "-1");
				final Term ante = TB.seqSub(services, e1.getTerm(), TB.zero(services), TB.add(services, e2.getTerm(), minusOne));
				final Term insert = TB.seqSingleton(services, e3.getTerm());
				final Term post = TB.seqSub(services, e1.getTerm(), TB.add(services, e2.getTerm(), TB.one(services)), TB.add(services, TB.seqLen(services, e1.getTerm()), minusOne));
				final Term put = TB.seqConcat(services, ante, TB.seqConcat(services, insert, post));
				result = new SLExpression(put);
				
			}
			break;
		}
		case SEQGET:
		case SEQCONCAT:
		case INDEXOF:
		{
			{
			switch ( LA(1)) {
			case SEQCONCAT:
			{
				tk2 = LT(1);
				match(SEQCONCAT);
				if ( inputState.guessing==0 ) {
					tk=tk2;
				}
				break;
			}
			case SEQGET:
			{
				tk3 = LT(1);
				match(SEQGET);
				if ( inputState.guessing==0 ) {
					tk=tk3;
				}
				break;
			}
			case INDEXOF:
			{
				tk4 = LT(1);
				match(INDEXOF);
				if ( inputState.guessing==0 ) {
					tk=tk4;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(LPAREN);
			e1=expression();
			match(COMMA);
			e2=expression();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = translator.translate(tk.getText(), SLExpression.class, services, e1, e2);
				
			}
			break;
		}
		default:
			boolean synPredMatched126 = false;
			if (((LA(1)==LPAREN) && (LA(2)==QUANTIFIER))) {
				int _m126 = mark();
				synPredMatched126 = true;
				inputState.guessing++;
				try {
					{
					match(LPAREN);
					match(QUANTIFIER);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched126 = false;
				}
				rewind(_m126);
inputState.guessing--;
			}
			if ( synPredMatched126 ) {
				t=specquantifiedexpression();
				if ( inputState.guessing==0 ) {
					result = new SLExpression(t);
				}
			}
			else {
				boolean synPredMatched128 = false;
				if (((LA(1)==LPAREN) && (LA(2)==BSUM))) {
					int _m128 = mark();
					synPredMatched128 = true;
					inputState.guessing++;
					try {
						{
						match(LPAREN);
						match(BSUM);
						}
					}
					catch (RecognitionException pe) {
						synPredMatched128 = false;
					}
					rewind(_m128);
inputState.guessing--;
				}
				if ( synPredMatched128 ) {
					result=bsumterm();
				}
				else {
					boolean synPredMatched130 = false;
					if (((LA(1)==LPAREN) && (LA(2)==SEQDEF))) {
						int _m130 = mark();
						synPredMatched130 = true;
						inputState.guessing++;
						try {
							{
							match(LPAREN);
							match(SEQDEF);
							}
						}
						catch (RecognitionException pe) {
							synPredMatched130 = false;
						}
						rewind(_m130);
inputState.guessing--;
					}
					if ( synPredMatched130 ) {
						result=seqdefterm();
					}
					else {
						boolean synPredMatched137 = false;
						if (((LA(1)==LPAREN) && (LA(2)==LBLNEG))) {
							int _m137 = mark();
							synPredMatched137 = true;
							inputState.guessing++;
							try {
								{
								match(LPAREN);
								match(LBLNEG);
								}
							}
							catch (RecognitionException pe) {
								synPredMatched137 = false;
							}
							rewind(_m137);
inputState.guessing--;
						}
						if ( synPredMatched137 ) {
							match(LPAREN);
							lblneg = LT(1);
							match(LBLNEG);
							match(IDENT);
							result=expression();
							match(RPAREN);
							if ( inputState.guessing==0 ) {
								
									    addIgnoreWarning("\\lblneg",lblneg);
									
							}
						}
						else {
							boolean synPredMatched139 = false;
							if (((LA(1)==LPAREN) && (LA(2)==LBLPOS))) {
								int _m139 = mark();
								synPredMatched139 = true;
								inputState.guessing++;
								try {
									{
									match(LPAREN);
									match(LBLPOS);
									}
								}
								catch (RecognitionException pe) {
									synPredMatched139 = false;
								}
								rewind(_m139);
inputState.guessing--;
							}
							if ( synPredMatched139 ) {
								match(LPAREN);
								lblpos = LT(1);
								match(LBLPOS);
								match(IDENT);
								result=expression();
								match(RPAREN);
								if ( inputState.guessing==0 ) {
									
										    addIgnoreWarning("\\lblpos",lblpos);
										
								}
							}
							else if ((LA(1)==LPAREN) && (_tokenSet_0.member(LA(2)))) {
								match(LPAREN);
								result=expression();
								match(RPAREN);
							}
						else {
							throw new NoViableAltException(LT(1), getFilename());
						}
						}}}}}
						return result;
					}
					
	public final void new_expr() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		KeYJavaType typ = null;
		ImmutableList<SLExpression> params;
		
		
		match(NEW);
		typ=type();
		{
		switch ( LA(1)) {
		case LPAREN:
		{
			match(LPAREN);
			{
			switch ( LA(1)) {
			case FALSE:
			case NEW:
			case NULL:
			case THIS:
			case TRUE:
			case BACKUP:
			case BITWISENOT:
			case CREATED:
			case DURATION:
			case ELEMTYPE:
			case FRESH:
			case INDEX:
			case INV:
			case INVARIANT_FOR:
			case IS_INITIALIZED:
			case LBRACE:
			case LOCKSET:
			case MINUS:
			case NONNULLELEMENTS:
			case NOT:
			case NOT_MODIFIED:
			case OLD:
			case PLUS:
			case PRE:
			case REACH:
			case REACHLOCS:
			case RESULT:
			case SPACE:
			case STRING_EQUAL:
			case TRANSACTIONUPDATED:
			case TYPEOF:
			case TYPE_SMALL:
			case VALUES:
			case WORKINGSPACE:
			case LOCSET:
			case EMPTYSET:
			case SINGLETON:
			case UNION:
			case INTERSECT:
			case SETMINUS:
			case ALLFIELDS:
			case ALLOBJECTS:
			case UNIONINF:
			case DISJOINT:
			case SUBSET:
			case NEWELEMSFRESH:
			case SEQGET:
			case SEQEMPTY:
			case SEQSINGLETON:
			case SEQCONCAT:
			case SEQSUB:
			case SEQREVERSE:
			case SEQREPLACE:
			case INDEXOF:
			case DL_ESCAPE:
			case LPAREN:
			case IDENT:
			case HEXNUMERAL:
			case DIGITS:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case INFORMAL_DESCRIPTION:
			case UNION_2:
			{
				params=expressionlist();
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			break;
		}
		case LBRACKET:
		{
			array_dimensions();
			{
			switch ( LA(1)) {
			case LBRACE:
			{
				array_initializer();
				break;
			}
			case EOF:
			case INSTANCEOF:
			case AND:
			case COLON:
			case COMMA:
			case DIV:
			case DOT:
			case DOTDOT:
			case EQUAL_SINGLE:
			case GEQ:
			case GT:
			case IMPLIES:
			case IMPLIESBACKWARD:
			case INCLUSIVEOR:
			case LARROW:
			case LEQ:
			case LOGICALAND:
			case LOGICALOR:
			case MINUS:
			case MOD:
			case MULT:
			case PLUS:
			case QUESTIONMARK:
			case RBRACE:
			case SEMI:
			case SHIFTLEFT:
			case SHIFTRIGHT:
			case ST:
			case SUCH_THAT:
			case UNSIGNEDSHIFTRIGHT:
			case XOR:
			case MEASURED_BY:
			case FROM:
			case TO:
			case IF:
			case EQV_ANTIV:
			case EQ_NEQ:
			case LT:
			case LPAREN:
			case RPAREN:
			case LBRACKET:
			case RBRACKET:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
				
				raiseNotSupported("'new' within specifications"); 
			
		}
	}
	
	public final void array_initializer() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		ImmutableList<SLExpression> init;
		
		
		match(LBRACE);
		init=expressionlist();
		match(RBRACE);
		if ( inputState.guessing==0 ) {
			
			raiseNotSupported("array initializer");
			
		}
	}
	
	public final SLExpression  transactionUpdated() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  tk = null;
		
		SLExpression expr;
		String fieldName = "<transactionConditionallyUpdated>";
		
		
		tk = LT(1);
		match(TRANSACTIONUPDATED);
		match(LPAREN);
		expr=expression();
		match(RPAREN);
		if ( inputState.guessing==0 ) {
			
			result = lookupIdentifier(fieldName, expr, null, tk);
			
		}
		return result;
	}
	
	public final ImmutableList<SLExpression>  expressionlist() throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<SLExpression> result=ImmutableSLList.<SLExpression>nil();
		
		
		SLExpression expr;
		
		
		expr=expression();
		if ( inputState.guessing==0 ) {
			result = result.append(expr);
		}
		{
		_loop117:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				expr=expression();
				if ( inputState.guessing==0 ) {
					result = result.append(expr);
				}
			}
			else {
				break _loop117;
			}
			
		} while (true);
		}
		return result;
	}
	
	public final KeYJavaType  type() throws RecognitionException, TokenStreamException, SLTranslationException {
		KeYJavaType t = null;
		
		
		switch ( LA(1)) {
		case BOOLEAN:
		case BYTE:
		case INT:
		case LONG:
		case SHORT:
		case VOID:
		case BIGINT:
		case FREE:
		case REAL:
		case LOCSET:
		case SEQ:
		{
			t=builtintype();
			break;
		}
		case IDENT:
		{
			t=referencetype();
			break;
		}
		case TYPE:
		{
			match(TYPE);
			if ( inputState.guessing==0 ) {
				
					    raiseNotSupported("\\TYPE");
					
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return t;
	}
	
	public final void array_dimensions() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		array_dimension();
	}
	
	public final void array_dimension() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		SLExpression length;
		
		
		match(LBRACKET);
		{
		switch ( LA(1)) {
		case FALSE:
		case NEW:
		case NULL:
		case THIS:
		case TRUE:
		case BACKUP:
		case BITWISENOT:
		case CREATED:
		case DURATION:
		case ELEMTYPE:
		case FRESH:
		case INDEX:
		case INV:
		case INVARIANT_FOR:
		case IS_INITIALIZED:
		case LBRACE:
		case LOCKSET:
		case MINUS:
		case NONNULLELEMENTS:
		case NOT:
		case NOT_MODIFIED:
		case OLD:
		case PLUS:
		case PRE:
		case REACH:
		case REACHLOCS:
		case RESULT:
		case SPACE:
		case STRING_EQUAL:
		case TRANSACTIONUPDATED:
		case TYPEOF:
		case TYPE_SMALL:
		case VALUES:
		case WORKINGSPACE:
		case LOCSET:
		case EMPTYSET:
		case SINGLETON:
		case UNION:
		case INTERSECT:
		case SETMINUS:
		case ALLFIELDS:
		case ALLOBJECTS:
		case UNIONINF:
		case DISJOINT:
		case SUBSET:
		case NEWELEMSFRESH:
		case SEQGET:
		case SEQEMPTY:
		case SEQSINGLETON:
		case SEQCONCAT:
		case SEQSUB:
		case SEQREVERSE:
		case SEQREPLACE:
		case INDEXOF:
		case DL_ESCAPE:
		case LPAREN:
		case IDENT:
		case HEXNUMERAL:
		case DIGITS:
		case CHAR_LITERAL:
		case STRING_LITERAL:
		case INFORMAL_DESCRIPTION:
		case UNION_2:
		{
			length=expression();
			break;
		}
		case RBRACKET:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		match(RBRACKET);
	}
	
	public final SLExpression  javaliteral() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  l = null;
		
		switch ( LA(1)) {
		case HEXNUMERAL:
		case DIGITS:
		{
			result=integerliteral();
			break;
		}
		case STRING_LITERAL:
		{
			l = LT(1);
			match(STRING_LITERAL);
			if ( inputState.guessing==0 ) {
				
					    Term charListTerm
					       = services.getTypeConverter()
					                 .convertToLogicElement(
					                 	new StringLiteral("\"" + l.getText() + "\""));
					    Function strPool 
					    	= (Function) services.getNamespaces()
					    	                     .functions()
					    	                     .lookup(CharListLDT.STRINGPOOL_NAME);
					    if(strPool == null) {
					        raiseError("string literals used in specification, "
					                   + "but string pool function not found");
					    }
					    Term stringTerm = TB.func(strPool, charListTerm);
					    return new SLExpression(stringTerm, 
					                            javaInfo.getKeYJavaType("java.lang.String"));
					
			}
			break;
		}
		case CHAR_LITERAL:
		{
			match(CHAR_LITERAL);
			if ( inputState.guessing==0 ) {
				
					    raiseNotSupported("character literals");
					
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return result;
	}
	
	public final SLExpression  integerliteral() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		switch ( LA(1)) {
		case DIGITS:
		{
			result=decimalintegerliteral();
			break;
		}
		case HEXNUMERAL:
		{
			result=hexintegerliteral();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return result;
	}
	
	public final SLExpression  decimalintegerliteral() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		
		result=decimalnumeral();
		return result;
	}
	
	public final SLExpression  hexintegerliteral() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  n = null;
		
		n = LT(1);
		match(HEXNUMERAL);
		if ( inputState.guessing==0 ) {
			
				BigInteger decInteger = new BigInteger(n.getText(), 16);
				result = new SLExpression(TB.zTerm(services, decInteger.toString()),
				                          javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT));
			
		}
		return result;
	}
	
	public final SLExpression  decimalnumeral() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  n = null;
		
		n = LT(1);
		match(DIGITS);
		if ( inputState.guessing==0 ) {
			
				result = new SLExpression(TB.zTerm(services,n.getText()),
				                          javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT));
			
		}
		return result;
	}
	
	public final Term  specquantifiedexpression() throws RecognitionException, TokenStreamException, SLTranslationException {
		Term result = null;
		
		Token  q = null;
		
		SLExpression expr;
		Term p = TB.tt();
		boolean nullable = false;
		Pair<KeYJavaType,ImmutableList<LogicVariable>> declVars = null;
		
		
		match(LPAREN);
		q = LT(1);
		match(QUANTIFIER);
		{
		switch ( LA(1)) {
		case NULLABLE:
		case NON_NULL:
		{
			nullable=boundvarmodifiers();
			break;
		}
		case BOOLEAN:
		case BYTE:
		case INT:
		case LONG:
		case SHORT:
		case VOID:
		case BIGINT:
		case FREE:
		case REAL:
		case TYPE:
		case LOCSET:
		case SEQ:
		case IDENT:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		declVars=quantifiedvardecls();
		match(SEMI);
		if ( inputState.guessing==0 ) {
			
				    resolverManager.pushLocalVariablesNamespace();
				    resolverManager.putIntoTopLocalVariablesNamespace(declVars.second, declVars.first);
				
		}
		{
		boolean synPredMatched149 = false;
		if (((_tokenSet_0.member(LA(1))) && (_tokenSet_5.member(LA(2))))) {
			int _m149 = mark();
			synPredMatched149 = true;
			inputState.guessing++;
			try {
				{
				predicate();
				match(SEMI);
				}
			}
			catch (RecognitionException pe) {
				synPredMatched149 = false;
			}
			rewind(_m149);
inputState.guessing--;
		}
		if ( synPredMatched149 ) {
			p=predicate();
			match(SEMI);
		}
		else if ((LA(1)==SEMI)) {
			match(SEMI);
		}
		else if ((_tokenSet_0.member(LA(1))) && (_tokenSet_6.member(LA(2)))) {
		}
		else {
			throw new NoViableAltException(LT(1), getFilename());
		}
		
		}
		expr=expression();
		if ( inputState.guessing==0 ) {
			
				    resolverManager.popLocalVariablesNamespace();
				    
				    p = TB.convertToFormula(p, services);
				    result = translator.translate(q.getText(), Term.class, p, expr.getTerm(), declVars.first, declVars.second, nullable, services);
				
		}
		match(RPAREN);
		return result;
	}
	
	public final SLExpression  bsumterm() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  q = null;
		
		SLExpression a = null;
		SLExpression b = null;
		SLExpression t = null;
		Pair<KeYJavaType,ImmutableList<LogicVariable>> decls = null;
		
		
		try {      // for error handling
			match(LPAREN);
			q = LT(1);
			match(BSUM);
			decls=quantifiedvardecls();
			if ( inputState.guessing==0 ) {
					    
				resolverManager.pushLocalVariablesNamespace();
				resolverManager.putIntoTopLocalVariablesNamespace(decls.second, decls.first);
				
			}
			match(SEMI);
			{
			a=expression();
			match(SEMI);
			b=expression();
			match(SEMI);
			t=expression();
			}
			if ( inputState.guessing==0 ) {
				
				result = translator.translate(q.getText(), SLExpression.class, a, b, t, decls.first, decls.second, services);
				resolverManager.popLocalVariablesNamespace();
				
			}
			match(RPAREN);
		}
		catch (SLTranslationException ex) {
			if (inputState.guessing==0) {
				
				resolverManager.popLocalVariablesNamespace();
				throw ex;
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final SLExpression  seqdefterm() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  q = null;
		
		SLExpression a = null;
		SLExpression b = null;
		SLExpression t = null;
		Pair<KeYJavaType,ImmutableList<LogicVariable>> decls = null;
		
		
		try {      // for error handling
			match(LPAREN);
			q = LT(1);
			match(SEQDEF);
			decls=quantifiedvardecls();
			if ( inputState.guessing==0 ) {
					    
				resolverManager.pushLocalVariablesNamespace();
				resolverManager.putIntoTopLocalVariablesNamespace(decls.second, decls.first);
				
			}
			match(SEMI);
			{
			a=expression();
			match(SEMI);
			b=expression();
			match(SEMI);
			t=expression();
			}
			if ( inputState.guessing==0 ) {
				
				result = translator.translate(q.getText(), SLExpression.class, a, b, t, decls.first, decls.second, services);
				resolverManager.popLocalVariablesNamespace();
				
			}
			match(RPAREN);
		}
		catch (SLTranslationException ex) {
			if (inputState.guessing==0) {
				
				resolverManager.popLocalVariablesNamespace();
				throw ex;
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final SLExpression  oldexpression() throws RecognitionException, TokenStreamException, SLTranslationException {
		SLExpression result=null;
		
		Token  id = null;
		KeYJavaType typ;
		
		{
		switch ( LA(1)) {
		case PRE:
		{
			match(PRE);
			match(LPAREN);
			result=expression();
			match(RPAREN);
			break;
		}
		case OLD:
		{
			match(OLD);
			match(LPAREN);
			result=expression();
			{
			switch ( LA(1)) {
			case COMMA:
			{
				match(COMMA);
				id = LT(1);
				match(IDENT);
				break;
			}
			case RPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
			if (atPres == null || atPres.get(getBaseHeap()) == null) {
			raiseError("JML construct " +
			"\\old not allowed in this context.");
			}
			
			if (id != null) addIgnoreWarning("\\old with label",id);
			
			typ = result.getType();
			if(typ != null) {
			result = new SLExpression(convertToOld(result.getTerm()), 
			result.getType());
			} else {
			result = new SLExpression(convertToOld(result.getTerm()));
			}
			
		}
		return result;
	}
	
	public final Pair<KeYJavaType,ImmutableList<LogicVariable>>  quantifiedvardecls() throws RecognitionException, TokenStreamException, SLTranslationException {
		Pair<KeYJavaType,ImmutableList<LogicVariable>> result = null;
		
		
		KeYJavaType t = null;
		ImmutableList<LogicVariable> vars = ImmutableSLList.<LogicVariable>nil();
		LogicVariable v = null;
		
		
		t=typespec();
		v=quantifiedvariabledeclarator(t);
		if ( inputState.guessing==0 ) {
			vars = vars.append(v);
		}
		{
		_loop159:
		do {
			if ((LA(1)==COMMA)) {
				match(COMMA);
				v=quantifiedvariabledeclarator(t);
				if ( inputState.guessing==0 ) {
					vars = vars.append(v);
				}
			}
			else {
				break _loop159;
			}
			
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				    result = new Pair<KeYJavaType,ImmutableList<LogicVariable>>(t, vars);
				
		}
		return result;
	}
	
	public final boolean  boundvarmodifiers() throws RecognitionException, TokenStreamException, SLTranslationException {
		boolean nullable = false;
		
		
		switch ( LA(1)) {
		case NON_NULL:
		{
			match(NON_NULL);
			break;
		}
		case NULLABLE:
		{
			match(NULLABLE);
			if ( inputState.guessing==0 ) {
				nullable = true;
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return nullable;
	}
	
	public final LogicVariable  quantifiedvariabledeclarator(
		KeYJavaType t
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		LogicVariable v = null;
		
		Token  id = null;
		
		int dim = 0;
		KeYJavaType varType = null;
		
		
		id = LT(1);
		match(IDENT);
		{
		switch ( LA(1)) {
		case LBRACKET:
		{
			dim=dims();
			break;
		}
		case COMMA:
		case SEMI:
		{
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			
				  if (dim > 0) {
				    String fullName;
				    if (t.getJavaType() instanceof ArrayType) {
					fullName = ((ArrayType) t.getJavaType()).getAlternativeNameRepresentation();
				    } else {
					fullName = t.getFullName();
				    }
				    for (int i=0; i < dim; i++) {
					fullName += "[]";
				    }
				    
				    varType = javaInfo.getKeYJavaType(fullName);
				  } else {
					  varType = t;
				  }
				  
				  v = new LogicVariable(new Name(id.getText()), varType.getSort());
			
		}
		return v;
	}
	
	public final int  dims() throws RecognitionException, TokenStreamException, SLTranslationException {
		int dimension = 0;
		
		
		{
		int _cnt165=0;
		_loop165:
		do {
			if ((LA(1)==LBRACKET)) {
				match(LBRACKET);
				match(RBRACKET);
				if ( inputState.guessing==0 ) {
					dimension++;
				}
			}
			else {
				if ( _cnt165>=1 ) { break _loop165; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt165++;
		} while (true);
		}
		return dimension;
	}
	
	public final KeYJavaType  builtintype() throws RecognitionException, TokenStreamException, SLTranslationException {
		KeYJavaType type = null;
		
		
		{
		switch ( LA(1)) {
		case BYTE:
		{
			match(BYTE);
			if ( inputState.guessing==0 ) {
				
						type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_BYTE);
					
			}
			break;
		}
		case SHORT:
		{
			match(SHORT);
			if ( inputState.guessing==0 ) {
				
						type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_SHORT);
					
			}
			break;
		}
		case INT:
		{
			match(INT);
			if ( inputState.guessing==0 ) {
				
						type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_INT);
					
			}
			break;
		}
		case LONG:
		{
			match(LONG);
			if ( inputState.guessing==0 ) {
				
						type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_LONG);
					
			}
			break;
		}
		case BOOLEAN:
		{
			match(BOOLEAN);
			if ( inputState.guessing==0 ) {
				
						type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
					
			}
			break;
		}
		case VOID:
		{
			match(VOID);
			if ( inputState.guessing==0 ) {
				
						type = KeYJavaType.VOID_TYPE;
					
			}
			break;
		}
		case BIGINT:
		{
			match(BIGINT);
			if ( inputState.guessing==0 ) {
				
						type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_BIGINT);
					
			}
			break;
		}
		case REAL:
		{
			match(REAL);
			if ( inputState.guessing==0 ) {
				
						raiseNotSupported("\\real");
					
			}
			break;
		}
		case LOCSET:
		{
			match(LOCSET);
			if ( inputState.guessing==0 ) {
				
				type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_LOCSET);
				
			}
			break;
		}
		case SEQ:
		{
			match(SEQ);
			if ( inputState.guessing==0 ) {
				
				type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_SEQ);
				
			}
			break;
		}
		case FREE:
		{
			match(FREE);
			if ( inputState.guessing==0 ) {
				type = javaInfo.getKeYJavaType(PrimitiveType.JAVA_FREE_ADT);
			}
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		}
		return type;
	}
	
	public final String  name() throws RecognitionException, TokenStreamException, SLTranslationException {
		String result = "";
		
		Token  id = null;
		Token  id1 = null;
		
		id = LT(1);
		match(IDENT);
		if ( inputState.guessing==0 ) {
			result += id.getText();
		}
		{
		_loop174:
		do {
			if ((LA(1)==DOT)) {
				match(DOT);
				id1 = LT(1);
				match(IDENT);
				if ( inputState.guessing==0 ) {
					result += "." + id1.getText();
				}
			}
			else {
				break _loop174;
			}
			
		} while (true);
		}
		return result;
	}
	
	
	public static final String[] _tokenNames = {
		"<0>",
		"EOF",
		"<2>",
		"NULL_TREE_LOOKAHEAD",
		"\"boolean\"",
		"\"byte\"",
		"\"false\"",
		"\"instanceof\"",
		"\"int\"",
		"\"long\"",
		"\"new\"",
		"\"null\"",
		"\"short\"",
		"\"super\"",
		"\"this\"",
		"\"true\"",
		"\"void\"",
		"\"accessible\"",
		"\"assignable\"",
		"\"ensures\"",
		"\"declassify\"",
		"\"depends\"",
		"\"represents\"",
		"\"requires\"",
		"\"respects\"",
		"\"secure_for\"",
		"\"signals\"",
		"\"signals_only\"",
		"\"nullable\"",
		"\"non_null\"",
		"\"breaks\"",
		"\"continues\"",
		"\"returns\"",
		"AND",
		"BACKUP",
		"BIGINT",
		"BITWISENOT",
		"BSUM",
		"COLON",
		"COMMA",
		"CREATED",
		"CURRENT_MEMORY_AREA",
		"DIV",
		"DOT",
		"DOTDOT",
		"DURATION",
		"ELEMTYPE",
		"EQUAL_SINGLE",
		"EVERYTHING",
		"FRESH",
		"FREE",
		"GEQ",
		"GT",
		"IMPLIES",
		"IMPLIESBACKWARD",
		"IN_IMMORTAL_MEMORY",
		"IN_OUTER_SCOPE",
		"INCLUSIVEOR",
		"INDEX",
		"INTO",
		"INV",
		"INVARIANT_FOR",
		"IS_INITIALIZED",
		"LARROW",
		"LBLNEG",
		"LBLPOS",
		"LBRACE",
		"LEQ",
		"LOCKSET",
		"LOGICALAND",
		"LOGICALOR",
		"MAX_SPACE",
		"MEMORY_AREA",
		"MINUS",
		"MOD",
		"MULT",
		"NONNULLELEMENTS",
		"NOT",
		"NOT_MODIFIED",
		"NOT_SPECIFIED",
		"NOTHING",
		"LESS_THAN_NOTHING",
		"STRICTLY_NOTHING",
		"OLD",
		"OTHER",
		"OUTER_SCOPE",
		"PLUS",
		"PRE",
		"PRIVATEDATA",
		"QUESTIONMARK",
		"RBRACE",
		"REACH",
		"REACHLOCS",
		"REAL",
		"REENTRANT_SCOPE",
		"RESULT",
		"RIGIDWORKINGSPACE",
		"SAME",
		"SEMI",
		"SHIFTLEFT",
		"SHIFTRIGHT",
		"SPACE",
		"STRING_EQUAL",
		"TRANSACTIONUPDATED",
		"TYPEOF",
		"TYPE_SMALL",
		"TYPE",
		"ST",
		"SUCH_THAT",
		"UNSIGNEDSHIFTRIGHT",
		"VALUES",
		"WORKINGSPACE",
		"XOR",
		"LOCSET",
		"EMPTYSET",
		"SINGLETON",
		"UNION",
		"INTERSECT",
		"SETMINUS",
		"ALLFIELDS",
		"ALLOBJECTS",
		"UNIONINF",
		"DISJOINT",
		"SUBSET",
		"NEWELEMSFRESH",
		"SEQ",
		"SEQGET",
		"SEQEMPTY",
		"SEQSINGLETON",
		"SEQCONCAT",
		"SEQSUB",
		"SEQREVERSE",
		"SEQREPLACE",
		"INDEXOF",
		"SEQDEF",
		"MEASURED_BY",
		"FROM",
		"TO",
		"IF",
		"DL_ESCAPE",
		"EQV_ANTIV",
		"EQ_NEQ",
		"LT_DISPATCH",
		"LT",
		"an implicit identifier (letters only)",
		"`('",
		"`)'",
		"`['",
		"`]'",
		"QUANTIFIER",
		"a letter",
		"a digit",
		"a hexadecimal digit",
		"LETTERORDIGIT",
		"an identifier",
		"HEXNUMERAL",
		"DIGITS",
		"CHAR_LITERAL",
		"a string in double quotes",
		"ESC",
		"white space",
		"informal specification",
		"comment",
		"comment",
		"lexical pragma (see Sect. 4.2 of JML reference)",
		"UNION_2"
	};
	
	private static final long[] mk_tokenSet_0() {
		long[] data = { 8359350596880354368L, -2306190589763751404L, 148109396031L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = { 8359632071857065024L, -2306190589763653100L, 148109396031L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = { 1125934266651440L, 2306410357750497280L, 67108864L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	private static final long[] mk_tokenSet_3() {
		long[] data = { 8359350596880354368L, -2306190589767946220L, 148109396031L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_3 = new BitSet(mk_tokenSet_3());
	private static final long[] mk_tokenSet_4() {
		long[] data = { -684830825950093326L, -13979058561L, 148113375231L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_4 = new BitSet(mk_tokenSet_4());
	private static final long[] mk_tokenSet_5() {
		long[] data = { 8538382056596561904L, -17606232211841L, 148112062591L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_5 = new BitSet(mk_tokenSet_5());
	private static final long[] mk_tokenSet_6() {
		long[] data = { 8538382056596561904L, -17623412081025L, 148112324735L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_6 = new BitSet(mk_tokenSet_6());
	
	}
