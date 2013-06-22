// $ANTLR 2.7.7 (2006-11-01): "jmlpreparser.g" -> "KeYJMLPreParser.java"$

    package de.uka.ilkd.key.speclang.jml.pretranslation;
    
    import java.io.StringReader;
    import java.util.Iterator;
    
    import de.uka.ilkd.key.collection.*;
    import de.uka.ilkd.key.java.Position;
    import de.uka.ilkd.key.speclang.*;
    import de.uka.ilkd.key.speclang.translation.*;
    import de.uka.ilkd.key.ldt.HeapLDT;
    import de.uka.ilkd.key.logic.Name;
    import de.uka.ilkd.key.logic.TermBuilder;

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

public class KeYJMLPreParser extends antlr.LLkParser       implements KeYJMLPreParserTokenTypes
 {

    private KeYJMLPreLexer lexer;
    private SLTranslationExceptionManager excManager;
    private ImmutableSet<PositionedString> warnings 	
    	= DefaultImmutableSet.<PositionedString>nil();
    
    
    private KeYJMLPreParser(KeYJMLPreLexer lexer,
                            String fileName,
                            Position offsetPos) {
    	this(lexer);
    	this.lexer      = lexer;
    	this.excManager = new SLTranslationExceptionManager(this, 
    							    fileName, 
    							    offsetPos); 
    }
    
    
    public KeYJMLPreParser(String comment, 
    			   String fileName, 
    			   Position offsetPos) {
	this(new KeYJMLPreLexer(new StringReader(comment)), 
	     fileName, 
	     offsetPos); 
    }
       
        
    private PositionedString createPositionedString(String text, 
    						    Token t) {
    	return excManager.createPositionedString(text, t);
    }
    
    
    private void raiseError(String msg) throws SLTranslationException {
        throw excManager.createException(msg);
    }
    
    
    private void raiseNotSupported(String feature) 
    		throws SLTranslationException {    		
	PositionedString warning 
		= excManager.createPositionedString(feature + " not supported");
    	warnings = warnings.add(warning);
    }
        
    
    public ImmutableList<TextualJMLConstruct> parseClasslevelComment() 
    		throws SLTranslationException {
        try {
            return classlevel_comment();
        } catch(ANTLRException e) {
	    throw excManager.convertException(e);
        }
    }
    
    
    public ImmutableList<TextualJMLConstruct> parseMethodlevelComment() 
    		throws SLTranslationException {
        try {
            return methodlevel_comment();
        } catch(ANTLRException e) {
	    throw excManager.convertException(e);
        }
    }
    
    
    public ImmutableSet<PositionedString> getWarnings() {
    	return warnings;
    }

    private PositionedString flipHeaps(String declString, PositionedString result) {
      String t = result.text;
      String p = declString+" ";
      for(Name heapName : HeapLDT.VALID_HEAP_NAMES) {
        t = t.trim();
	String l = "<"+heapName+">";
        if(t.startsWith(l)) {
           p = l + p;
           t = t.substring(l.length());
        }
        result = new PositionedString(t, result.fileName, result.pos);
      }
      result = result.prepend(p);
      return result;
    }


protected KeYJMLPreParser(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
}

public KeYJMLPreParser(TokenBuffer tokenBuf) {
  this(tokenBuf,1);
}

protected KeYJMLPreParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
}

public KeYJMLPreParser(TokenStream lexer) {
  this(lexer,1);
}

public KeYJMLPreParser(ParserSharedInputState state) {
  super(state,1);
  tokenNames = _tokenNames;
}

	public final ImmutableList<TextualJMLConstruct>  classlevel_comment() throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result 
		 = ImmutableSLList.<TextualJMLConstruct>nil();
		
		
		ImmutableList<String> mods = ImmutableSLList.<String>nil();
		ImmutableList<TextualJMLConstruct> list;
		
		
		{
		_loop3:
		do {
			// nongreedy exit test
			if ((LA(1)==EOF)) break _loop3;
			if ((_tokenSet_0.member(LA(1)))) {
				mods=modifiers();
				list=classlevel_element(mods);
				if ( inputState.guessing==0 ) {
					
						    if(list!=null) {
						    	result = result.append(list); 
						    }
						
				}
			}
			else {
				break _loop3;
			}
			
		} while (true);
		}
		match(Token.EOF_TYPE);
		return result;
	}
	
	public final ImmutableList<String>  modifiers() throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<String> result = ImmutableSLList.<String>nil();
		
		
		String s;
		
		
		{
		_loop15:
		do {
			if ((_tokenSet_1.member(LA(1)))) {
				s=modifier();
				if ( inputState.guessing==0 ) {
					result = result.append(s);
				}
			}
			else {
				break _loop15;
			}
			
		} while (true);
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  classlevel_element(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		switch ( LA(1)) {
		case INVARIANT:
		case INVARIANT_RED:
		{
			result=class_invariant(mods);
			break;
		}
		case REPRESENTS:
		case REPRESENTS_RED:
		{
			result=represents_clause(mods);
			break;
		}
		case CONSTRAINT:
		case CONSTRAINT_RED:
		{
			result=history_constraint(mods);
			break;
		}
		case INITIALLY:
		{
			result=initially_clause(mods);
			break;
		}
		case AXIOM:
		{
			result=class_axiom(mods);
			break;
		}
		case MONITORS_FOR:
		{
			result=monitors_for_clause(mods);
			break;
		}
		case READABLE:
		{
			result=readable_if_clause(mods);
			break;
		}
		case WRITABLE:
		{
			result=writable_if_clause(mods);
			break;
		}
		case IN:
		case IN_RED:
		case MAPS:
		case MAPS_RED:
		{
			result=datagroup_clause(mods);
			break;
		}
		case SET:
		{
			result=set_statement(mods);
			break;
		}
		case ASSERT:
		case ASSERT_REDUNDANTLY:
		{
			result=assert_statement(mods);
			break;
		}
		case ASSUME:
		case ASSUME_REDUNDANTLY:
		{
			result=assume_statement(mods);
			break;
		}
		case NOWARN:
		{
			result=nowarn_pragma(mods);
			break;
		}
		case EOF:
		{
			match(Token.EOF_TYPE);
			break;
		}
		default:
			boolean synPredMatched6 = false;
			if (((LA(1)==ACCESSIBLE||LA(1)==ACCESSIBLE_REDUNDANTLY))) {
				int _m6 = mark();
				synPredMatched6 = true;
				inputState.guessing++;
				try {
					{
					depends_clause(mods);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched6 = false;
				}
				rewind(_m6);
inputState.guessing--;
			}
			if ( synPredMatched6 ) {
				result=depends_clause(mods);
			}
			else if ((_tokenSet_2.member(LA(1)))) {
				result=method_specification(mods);
			}
			else {
				boolean synPredMatched8 = false;
				if (((LA(1)==IDENT))) {
					int _m8 = mark();
					synPredMatched8 = true;
					inputState.guessing++;
					try {
						{
						method_declaration(mods);
						}
					}
					catch (RecognitionException pe) {
						synPredMatched8 = false;
					}
					rewind(_m8);
inputState.guessing--;
				}
				if ( synPredMatched8 ) {
					result=method_declaration(mods);
				}
				else if ((LA(1)==IDENT)) {
					result=field_declaration(mods);
				}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			}}
			return result;
		}
		
	public final ImmutableList<TextualJMLConstruct>  class_invariant(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		String name = null;
		
		
		invariant_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				TextualJMLClassInv inv = name == null ? new TextualJMLClassInv(mods, ps) : new TextualJMLClassInv(mods, ps, name);
				result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(inv);
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  depends_clause(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		accessible_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				TextualJMLDepends d 
					= new TextualJMLDepends(mods, ps.prepend("depends "));
				result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(d);
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  method_specification(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		ImmutableList<TextualJMLConstruct> list = ImmutableSLList.<TextualJMLConstruct>nil();
		
		
		{
		_loop24:
		do {
			if ((LA(1)==ALSO||LA(1)==FOR_EXAMPLE||LA(1)==IMPLIES_THAT)) {
				also_keyword();
			}
			else {
				break _loop24;
			}
			
		} while (true);
		}
		result=spec_case(mods);
		{
		_loop28:
		do {
			if ((LA(1)==ALSO||LA(1)==FOR_EXAMPLE||LA(1)==IMPLIES_THAT)) {
				{
				int _cnt27=0;
				_loop27:
				do {
					if ((LA(1)==ALSO||LA(1)==FOR_EXAMPLE||LA(1)==IMPLIES_THAT)) {
						also_keyword();
					}
					else {
						if ( _cnt27>=1 ) { break _loop27; } else {throw new NoViableAltException(LT(1), getFilename());}
					}
					
					_cnt27++;
				} while (true);
				}
				list=spec_case(ImmutableSLList.<String>nil());
				if ( inputState.guessing==0 ) {
					
						    result = result.append(list); 
						
				}
			}
			else {
				break _loop28;
			}
			
		} while (true);
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  method_declaration(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		Token  type = null;
		Token  name = null;
		Token  params = null;
		Token  body = null;
		Token  semi = null;
		
		StringBuffer sb = new StringBuffer();
		String s;
		
		
		type = LT(1);
		match(IDENT);
		if ( inputState.guessing==0 ) {
			sb.append(type.getText() + " ");
		}
		name = LT(1);
		match(IDENT);
		if ( inputState.guessing==0 ) {
			sb.append(name.getText());
		}
		params = LT(1);
		match(PARAM_LIST);
		if ( inputState.guessing==0 ) {
			sb.append(params.getText());
		}
		{
		switch ( LA(1)) {
		case BODY:
		{
			body = LT(1);
			match(BODY);
			if ( inputState.guessing==0 ) {
				sb.append(body.getText());
			}
			break;
		}
		case SEMICOLON:
		{
			semi = LT(1);
			match(SEMICOLON);
			if ( inputState.guessing==0 ) {
				sb.append(semi.getText());
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
			
			PositionedString ps = createPositionedString(sb.toString(), type);
				TextualJMLMethodDecl md 
					= new TextualJMLMethodDecl(mods, ps, name.getText());
				result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(md);
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  field_declaration(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		Token  type = null;
		Token  name = null;
		Token  init = null;
		Token  semi = null;
		
		StringBuffer sb = new StringBuffer();
		String s;
		
		
		type = LT(1);
		match(IDENT);
		if ( inputState.guessing==0 ) {
			sb.append(type.getText() + " ");
		}
		name = LT(1);
		match(IDENT);
		if ( inputState.guessing==0 ) {
			sb.append(name.getText());
		}
		{
		switch ( LA(1)) {
		case INITIALISER:
		{
			init = LT(1);
			match(INITIALISER);
			if ( inputState.guessing==0 ) {
				sb.append(init.getText());
			}
			break;
		}
		case SEMICOLON:
		{
			semi = LT(1);
			match(SEMICOLON);
			if ( inputState.guessing==0 ) {
				sb.append(semi.getText());
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
			
			PositionedString ps = createPositionedString(sb.toString(), type);
				TextualJMLFieldDecl fd = new TextualJMLFieldDecl(mods, ps);
				result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(fd);
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  represents_clause(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		represents_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				TextualJMLRepresents rc 
					= new TextualJMLRepresents(mods, ps.prepend("represents "));
				result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(rc);
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  history_constraint(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		constraint_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("history constraints");
				result = ImmutableSLList.<TextualJMLConstruct>nil();
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  initially_clause(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		match(INITIALLY);
		ps=expression();
		if ( inputState.guessing==0 ) {
			
			TextualJMLInitially ini = new TextualJMLInitially(mods, ps);
			result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(ini);
			for (String s: mods) {
			if (!(s.equals("public")||s.equals("private")||s.equals("protected"))) 
			raiseNotSupported("modifier "+s+" in initially clause");
			}
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  class_axiom(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		match(AXIOM);
		ps=expression();
		if ( inputState.guessing==0 ) {
			
			TextualJMLClassAxiom ax = new TextualJMLClassAxiom(mods, ps);
			result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(ax);
			// axiom statements may not be prefixed with any modifiers (see Sect. 8 of the JML reference manual)
			if (!mods.isEmpty()) 
			raiseNotSupported("modifiers in axiom clause");
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  monitors_for_clause(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		match(MONITORS_FOR);
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("monitors_for clauses");
				result = ImmutableSLList.<TextualJMLConstruct>nil();    	
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  readable_if_clause(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		match(READABLE);
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("readable-if clauses");
				result = ImmutableSLList.<TextualJMLConstruct>nil();    	
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  writable_if_clause(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		match(WRITABLE);
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("writable-if clauses");
				result = ImmutableSLList.<TextualJMLConstruct>nil();    	
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  datagroup_clause(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		switch ( LA(1)) {
		case IN:
		case IN_RED:
		{
			in_group_clause();
			break;
		}
		case MAPS:
		case MAPS_RED:
		{
			maps_into_clause();
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  set_statement(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		match(SET);
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				TextualJMLSetStatement ss = new TextualJMLSetStatement(mods, ps);
				result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(ss);
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  assert_statement(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		assert_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				result = ImmutableSLList.<TextualJMLConstruct>nil().append(TextualJMLSpecCase.assert2blockContract(mods,ps));				       
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  assume_statement(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		assume_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
			raiseNotSupported("assume statements");
				result = ImmutableSLList.<TextualJMLConstruct>nil();        
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  nowarn_pragma(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		
		
		match(NOWARN);
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("nowarn pragmas");
				result = ImmutableSLList.<TextualJMLConstruct>nil();    	
			
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  methodlevel_comment() throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result 
		 = ImmutableSLList.<TextualJMLConstruct>nil();
		
		
		ImmutableList<String> mods = ImmutableSLList.<String>nil();
		ImmutableList<TextualJMLConstruct> list;
		
		
		{
		_loop11:
		do {
			if ((_tokenSet_3.member(LA(1)))) {
				mods=modifiers();
				list=methodlevel_element(mods);
				if ( inputState.guessing==0 ) {
					result = result.append(list);
				}
			}
			else {
				break _loop11;
			}
			
		} while (true);
		}
		match(Token.EOF_TYPE);
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  methodlevel_element(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		switch ( LA(1)) {
		case IDENT:
		{
			result=field_declaration(mods);
			break;
		}
		case SET:
		{
			result=set_statement(mods);
			break;
		}
		case LOOP_INVARIANT:
		case MAINTAINING:
		case MAINTAINING_REDUNDANTLY:
		case LOOP_INVARIANT_REDUNDANTLY:
		{
			result=loop_specification(mods);
			break;
		}
		case ASSERT:
		case ASSERT_REDUNDANTLY:
		{
			result=assert_statement(mods);
			break;
		}
		case ASSUME:
		case ASSUME_REDUNDANTLY:
		{
			result=assume_statement(mods);
			break;
		}
		case NOWARN:
		{
			result=nowarn_pragma(mods);
			break;
		}
		case ABSTRACT:
		case ACCESSIBLE:
		case ACCESSIBLE_REDUNDANTLY:
		case ALSO:
		case ASSIGNABLE:
		case ASSIGNABLE_RED:
		case BEHAVIOR:
		case BEHAVIOUR:
		case BREAKS:
		case BREAK_BEHAVIOR:
		case BREAK_BEHAVIOUR:
		case CAPTURES:
		case CAPTURES_RED:
		case CONTINUES:
		case CONTINUE_BEHAVIOR:
		case CONTINUE_BEHAVIOUR:
		case DIVERGES:
		case DIVERGES_RED:
		case DURATION:
		case DURATION_RED:
		case ENSURES:
		case ENSURES_RED:
		case EXCEPTIONAL_BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOUR:
		case FINAL:
		case FOR_EXAMPLE:
		case FORALL:
		case GHOST:
		case HELPER:
		case IMPLIES_THAT:
		case INSTANCE:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case MODEL:
		case MODIFIABLE:
		case MODIFIABLE_RED:
		case MODIFIES:
		case MODIFIES_RED:
		case NON_NULL:
		case NORMAL_BEHAVIOR:
		case NORMAL_BEHAVIOUR:
		case NULLABLE:
		case NULLABLE_BY_DEFAULT:
		case OLD:
		case PRIVATE:
		case PROTECTED:
		case PUBLIC:
		case PURE:
		case STRICTLY_PURE:
		case REQUIRES:
		case REQUIRES_RED:
		case RETURNS:
		case RETURN_BEHAVIOR:
		case RETURN_BEHAVIOUR:
		case SIGNALS:
		case SIGNALS_ONLY:
		case SIGNALS_ONLY_RED:
		case SIGNALS_RED:
		case SPEC_PROTECTED:
		case SPEC_PUBLIC:
		case SPEC_NAME:
		case STATIC:
		case WHEN:
		case WHEN_RED:
		case WORKING_SPACE:
		case WORKING_SPACE_RED:
		case NEST_START:
		case EXSURES:
		case EXSURES_RED:
		{
			result=block_specification(mods);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  loop_specification(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		PositionedString ps;
		TextualJMLLoopSpec ls = new TextualJMLLoopSpec(mods);
		result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(ls);
		
		
		ps=loop_invariant();
		if ( inputState.guessing==0 ) {
			ls.addInvariant(ps);
		}
		{
		_loop111:
		do {
			if ((_tokenSet_4.member(LA(1)))) {
				ps=loop_invariant();
				if ( inputState.guessing==0 ) {
					ls.addInvariant(ps);
				}
			}
			else if ((_tokenSet_5.member(LA(1)))) {
				ps=assignable_clause();
				if ( inputState.guessing==0 ) {
					ls.addAssignable(ps);
				}
			}
			else if (((LA(1) >= DECREASES && LA(1) <= DECREASING_REDUNDANTLY))) {
				ps=variant_function();
				if ( inputState.guessing==0 ) {
					ls.setVariant(ps);
				}
			}
			else {
				break _loop111;
			}
			
		} while (true);
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  block_specification(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		result=method_specification(mods);
		return result;
	}
	
	public final String  modifier() throws RecognitionException, TokenStreamException {
		String result = null;
		
		Token  abs = null;
		Token  fin = null;
		Token  gho = null;
		Token  hel = null;
		Token  ins = null;
		Token  mod = null;
		Token  nnu = null;
		Token  nul = null;
		Token  nld = null;
		Token  pri = null;
		Token  pro = null;
		Token  pub = null;
		Token  pur = null;
		Token  stp = null;
		Token  spr = null;
		Token  spu = null;
		Token  sta = null;
		
		switch ( LA(1)) {
		case ABSTRACT:
		{
			abs = LT(1);
			match(ABSTRACT);
			if ( inputState.guessing==0 ) {
				result = abs.getText();
			}
			break;
		}
		case FINAL:
		{
			fin = LT(1);
			match(FINAL);
			if ( inputState.guessing==0 ) {
				result = fin.getText();
			}
			break;
		}
		case GHOST:
		{
			gho = LT(1);
			match(GHOST);
			if ( inputState.guessing==0 ) {
				result = gho.getText();
			}
			break;
		}
		case HELPER:
		{
			hel = LT(1);
			match(HELPER);
			if ( inputState.guessing==0 ) {
				result = hel.getText();
			}
			break;
		}
		case INSTANCE:
		{
			ins = LT(1);
			match(INSTANCE);
			if ( inputState.guessing==0 ) {
				result = ins.getText();
			}
			break;
		}
		case MODEL:
		{
			mod = LT(1);
			match(MODEL);
			if ( inputState.guessing==0 ) {
				result = mod.getText();
			}
			break;
		}
		case NON_NULL:
		{
			nnu = LT(1);
			match(NON_NULL);
			if ( inputState.guessing==0 ) {
				result = nnu.getText();
			}
			break;
		}
		case NULLABLE:
		{
			nul = LT(1);
			match(NULLABLE);
			if ( inputState.guessing==0 ) {
				result = nul.getText();
			}
			break;
		}
		case NULLABLE_BY_DEFAULT:
		{
			nld = LT(1);
			match(NULLABLE_BY_DEFAULT);
			if ( inputState.guessing==0 ) {
				result = nld.getText();
			}
			break;
		}
		case PRIVATE:
		{
			pri = LT(1);
			match(PRIVATE);
			if ( inputState.guessing==0 ) {
				result = pri.getText();
			}
			break;
		}
		case PROTECTED:
		{
			pro = LT(1);
			match(PROTECTED);
			if ( inputState.guessing==0 ) {
				result = pro.getText();
			}
			break;
		}
		case PUBLIC:
		{
			pub = LT(1);
			match(PUBLIC);
			if ( inputState.guessing==0 ) {
				result = pub.getText();
			}
			break;
		}
		case PURE:
		{
			pur = LT(1);
			match(PURE);
			if ( inputState.guessing==0 ) {
				result = pur.getText();
			}
			break;
		}
		case STRICTLY_PURE:
		{
			stp = LT(1);
			match(STRICTLY_PURE);
			if ( inputState.guessing==0 ) {
				result = stp.getText();
			}
			break;
		}
		case SPEC_PROTECTED:
		{
			spr = LT(1);
			match(SPEC_PROTECTED);
			if ( inputState.guessing==0 ) {
				result = spr.getText();
			}
			break;
		}
		case SPEC_PUBLIC:
		{
			spu = LT(1);
			match(SPEC_PUBLIC);
			if ( inputState.guessing==0 ) {
				result = spu.getText();
			}
			break;
		}
		case STATIC:
		{
			sta = LT(1);
			match(STATIC);
			if ( inputState.guessing==0 ) {
				result = sta.getText();
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
	
	public final void invariant_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case INVARIANT:
		{
			match(INVARIANT);
			break;
		}
		case INVARIANT_RED:
		{
			match(INVARIANT_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final PositionedString  expression() throws RecognitionException, TokenStreamException {
		PositionedString result = null;
		
		Token  t = null;
		
		lexer.setExpressionMode(true);
		LT(1);
		lexer.setExpressionMode(false);
		
		
		t = LT(1);
		match(EXPRESSION);
		if ( inputState.guessing==0 ) {
			
				result = createPositionedString(t.getText(), t);
			
		}
		return result;
	}
	
/** Introduce a user-given name to axiom-like declarations. */
	public final String  axiom_name() throws RecognitionException, TokenStreamException, SLTranslationException {
		String result = null;
		
		Token  id = null;
		
		match(AXIOM_NAME_BEGIN);
		id = LT(1);
		match(IDENT);
		match(AXIOM_NAME_END);
		if ( inputState.guessing==0 ) {
			result = id.getText();
		}
		return result;
	}
	
	public final void also_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case ALSO:
		{
			match(ALSO);
			break;
		}
		case FOR_EXAMPLE:
		{
			match(FOR_EXAMPLE);
			break;
		}
		case IMPLIES_THAT:
		{
			match(IMPLIES_THAT);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final ImmutableList<TextualJMLConstruct>  spec_case(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		switch ( LA(1)) {
		case ACCESSIBLE:
		case ACCESSIBLE_REDUNDANTLY:
		case ASSIGNABLE:
		case ASSIGNABLE_RED:
		case BREAKS:
		case CAPTURES:
		case CAPTURES_RED:
		case CONTINUES:
		case DIVERGES:
		case DIVERGES_RED:
		case DURATION:
		case DURATION_RED:
		case ENSURES:
		case ENSURES_RED:
		case FORALL:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case MODIFIABLE:
		case MODIFIABLE_RED:
		case MODIFIES:
		case MODIFIES_RED:
		case OLD:
		case REQUIRES:
		case REQUIRES_RED:
		case RETURNS:
		case SIGNALS:
		case SIGNALS_ONLY:
		case SIGNALS_ONLY_RED:
		case SIGNALS_RED:
		case SPEC_NAME:
		case WHEN:
		case WHEN_RED:
		case WORKING_SPACE:
		case WORKING_SPACE_RED:
		case NEST_START:
		case EXSURES:
		case EXSURES_RED:
		{
			result=lightweight_spec_case(mods);
			break;
		}
		case ABSTRACT:
		case BEHAVIOR:
		case BEHAVIOUR:
		case BREAK_BEHAVIOR:
		case BREAK_BEHAVIOUR:
		case CONTINUE_BEHAVIOR:
		case CONTINUE_BEHAVIOUR:
		case EXCEPTIONAL_BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOUR:
		case FINAL:
		case GHOST:
		case HELPER:
		case INSTANCE:
		case MODEL:
		case NON_NULL:
		case NORMAL_BEHAVIOR:
		case NORMAL_BEHAVIOUR:
		case NULLABLE:
		case NULLABLE_BY_DEFAULT:
		case PRIVATE:
		case PROTECTED:
		case PUBLIC:
		case PURE:
		case STRICTLY_PURE:
		case RETURN_BEHAVIOR:
		case RETURN_BEHAVIOUR:
		case SPEC_PROTECTED:
		case SPEC_PUBLIC:
		case STATIC:
		{
			result=heavyweight_spec_case(mods);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  lightweight_spec_case(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		result=generic_spec_case(mods, Behavior.NONE);
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  heavyweight_spec_case(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		String s;
		
		
		{
		switch ( LA(1)) {
		case ABSTRACT:
		case FINAL:
		case GHOST:
		case HELPER:
		case INSTANCE:
		case MODEL:
		case NON_NULL:
		case NULLABLE:
		case NULLABLE_BY_DEFAULT:
		case PRIVATE:
		case PROTECTED:
		case PUBLIC:
		case PURE:
		case STRICTLY_PURE:
		case SPEC_PROTECTED:
		case SPEC_PUBLIC:
		case STATIC:
		{
			s=modifier();
			if ( inputState.guessing==0 ) {
				mods = mods.append(s);
			}
			break;
		}
		case BEHAVIOR:
		case BEHAVIOUR:
		case BREAK_BEHAVIOR:
		case BREAK_BEHAVIOUR:
		case CONTINUE_BEHAVIOR:
		case CONTINUE_BEHAVIOUR:
		case EXCEPTIONAL_BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOUR:
		case NORMAL_BEHAVIOR:
		case NORMAL_BEHAVIOUR:
		case RETURN_BEHAVIOR:
		case RETURN_BEHAVIOUR:
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
		case BEHAVIOR:
		case BEHAVIOUR:
		{
			result=behavior_spec_case(mods);
			break;
		}
		case BREAK_BEHAVIOR:
		case BREAK_BEHAVIOUR:
		{
			result=break_behavior_spec_case(mods);
			break;
		}
		case CONTINUE_BEHAVIOR:
		case CONTINUE_BEHAVIOUR:
		{
			result=continue_behavior_spec_case(mods);
			break;
		}
		case EXCEPTIONAL_BEHAVIOR:
		case EXCEPTIONAL_BEHAVIOUR:
		{
			result=exceptional_behavior_spec_case(mods);
			break;
		}
		case NORMAL_BEHAVIOR:
		case NORMAL_BEHAVIOUR:
		{
			result=normal_behavior_spec_case(mods);
			break;
		}
		case RETURN_BEHAVIOR:
		case RETURN_BEHAVIOUR:
		{
			result=return_behavior_spec_case(mods);
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
	
	public final ImmutableList<TextualJMLConstruct>  generic_spec_case(
		ImmutableList<String> mods, Behavior b
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result 
		 = ImmutableSLList.<TextualJMLConstruct>nil();
		
		
		ImmutableList<PositionedString> requires;
		
		
		{
		switch ( LA(1)) {
		case FORALL:
		case OLD:
		{
			spec_var_decls();
			break;
		}
		case ACCESSIBLE:
		case ACCESSIBLE_REDUNDANTLY:
		case ASSIGNABLE:
		case ASSIGNABLE_RED:
		case BREAKS:
		case CAPTURES:
		case CAPTURES_RED:
		case CONTINUES:
		case DIVERGES:
		case DIVERGES_RED:
		case DURATION:
		case DURATION_RED:
		case ENSURES:
		case ENSURES_RED:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case MODIFIABLE:
		case MODIFIABLE_RED:
		case MODIFIES:
		case MODIFIES_RED:
		case REQUIRES:
		case REQUIRES_RED:
		case RETURNS:
		case SIGNALS:
		case SIGNALS_ONLY:
		case SIGNALS_ONLY_RED:
		case SIGNALS_RED:
		case SPEC_NAME:
		case WHEN:
		case WHEN_RED:
		case WORKING_SPACE:
		case WORKING_SPACE_RED:
		case NEST_START:
		case EXSURES:
		case EXSURES_RED:
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
		case REQUIRES:
		case REQUIRES_RED:
		{
			requires=spec_header();
			{
			boolean synPredMatched46 = false;
			if (((_tokenSet_6.member(LA(1))))) {
				int _m46 = mark();
				synPredMatched46 = true;
				inputState.guessing++;
				try {
					{
					generic_spec_body(mods, b);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched46 = false;
				}
				rewind(_m46);
inputState.guessing--;
			}
			if ( synPredMatched46 ) {
				result=generic_spec_body(mods, b);
			}
			else if ((_tokenSet_7.member(LA(1)))) {
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
			if ( inputState.guessing==0 ) {
				
				if(result.isEmpty()) {
				result = result.append(new TextualJMLSpecCase(mods, b));
				}
				
				for(Iterator<TextualJMLConstruct> it = result.iterator(); 
				it.hasNext(); ) {
					TextualJMLSpecCase sc = (TextualJMLSpecCase) it.next();
				sc.addRequires(requires);
				}
				
			}
			break;
		}
		case ACCESSIBLE:
		case ACCESSIBLE_REDUNDANTLY:
		case ASSIGNABLE:
		case ASSIGNABLE_RED:
		case BREAKS:
		case CAPTURES:
		case CAPTURES_RED:
		case CONTINUES:
		case DIVERGES:
		case DIVERGES_RED:
		case DURATION:
		case DURATION_RED:
		case ENSURES:
		case ENSURES_RED:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case MODIFIABLE:
		case MODIFIABLE_RED:
		case MODIFIES:
		case MODIFIES_RED:
		case RETURNS:
		case SIGNALS:
		case SIGNALS_ONLY:
		case SIGNALS_ONLY_RED:
		case SIGNALS_RED:
		case SPEC_NAME:
		case WHEN:
		case WHEN_RED:
		case WORKING_SPACE:
		case WORKING_SPACE_RED:
		case NEST_START:
		case EXSURES:
		case EXSURES_RED:
		{
			result=generic_spec_body(mods, b);
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
	
	public final ImmutableList<TextualJMLConstruct>  behavior_spec_case(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		behavior_keyword();
		result=generic_spec_case(mods, Behavior.BEHAVIOR);
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  break_behavior_spec_case(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		break_behavior_keyword();
		result=generic_spec_case(mods, Behavior.BREAK_BEHAVIOR);
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  continue_behavior_spec_case(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		continue_behavior_keyword();
		result=generic_spec_case(mods, Behavior.CONTINUE_BEHAVIOR);
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  exceptional_behavior_spec_case(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		exceptional_behavior_keyword();
		result=generic_spec_case(mods, Behavior.EXCEPTIONAL_BEHAVIOR);
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  normal_behavior_spec_case(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		normal_behavior_keyword();
		result=generic_spec_case(mods, Behavior.NORMAL_BEHAVIOR);
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  return_behavior_spec_case(
		ImmutableList<String> mods
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		return_behavior_keyword();
		result=generic_spec_case(mods, Behavior.RETURN_BEHAVIOR);
		return result;
	}
	
	public final void behavior_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case BEHAVIOR:
		{
			match(BEHAVIOR);
			break;
		}
		case BEHAVIOUR:
		{
			match(BEHAVIOUR);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void normal_behavior_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case NORMAL_BEHAVIOR:
		{
			match(NORMAL_BEHAVIOR);
			break;
		}
		case NORMAL_BEHAVIOUR:
		{
			match(NORMAL_BEHAVIOUR);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void exceptional_behavior_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case EXCEPTIONAL_BEHAVIOR:
		{
			match(EXCEPTIONAL_BEHAVIOR);
			break;
		}
		case EXCEPTIONAL_BEHAVIOUR:
		{
			match(EXCEPTIONAL_BEHAVIOUR);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void spec_var_decls() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		PositionedString ps;
		
		
		{
		int _cnt49=0;
		_loop49:
		do {
			switch ( LA(1)) {
			case FORALL:
			{
				match(FORALL);
				ps=expression();
				break;
			}
			case OLD:
			{
				match(OLD);
				ps=expression();
				break;
			}
			default:
			{
				if ( _cnt49>=1 ) { break _loop49; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			}
			_cnt49++;
		} while (true);
		}
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("specification variables");
			
		}
	}
	
	public final ImmutableList<PositionedString>  spec_header() throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<PositionedString> result 
		 = ImmutableSLList.<PositionedString>nil();
		
		
		PositionedString ps;
		
		
		{
		int _cnt52=0;
		_loop52:
		do {
			if ((LA(1)==REQUIRES||LA(1)==REQUIRES_RED)) {
				ps=requires_clause();
				if ( inputState.guessing==0 ) {
					result = result.append(ps);
				}
			}
			else {
				if ( _cnt52>=1 ) { break _loop52; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt52++;
		} while (true);
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  generic_spec_body(
		ImmutableList<String> mods, Behavior b
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		TextualJMLSpecCase sc;
		
		
		switch ( LA(1)) {
		case ACCESSIBLE:
		case ACCESSIBLE_REDUNDANTLY:
		case ASSIGNABLE:
		case ASSIGNABLE_RED:
		case BREAKS:
		case CAPTURES:
		case CAPTURES_RED:
		case CONTINUES:
		case DIVERGES:
		case DIVERGES_RED:
		case DURATION:
		case DURATION_RED:
		case ENSURES:
		case ENSURES_RED:
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		case MODIFIABLE:
		case MODIFIABLE_RED:
		case MODIFIES:
		case MODIFIES_RED:
		case RETURNS:
		case SIGNALS:
		case SIGNALS_ONLY:
		case SIGNALS_ONLY_RED:
		case SIGNALS_RED:
		case SPEC_NAME:
		case WHEN:
		case WHEN_RED:
		case WORKING_SPACE:
		case WORKING_SPACE_RED:
		case EXSURES:
		case EXSURES_RED:
		{
			result=simple_spec_body(mods, b);
			break;
		}
		case NEST_START:
		{
			{
			match(NEST_START);
			result=generic_spec_case_seq(mods, b);
			match(NEST_END);
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
	
	public final PositionedString  requires_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		requires_keyword();
		result=expression();
		if ( inputState.guessing==0 ) {
			result = flipHeaps("requires", result);
		}
		return result;
	}
	
	public final void requires_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case REQUIRES:
		{
			match(REQUIRES);
			break;
		}
		case REQUIRES_RED:
		{
			match(REQUIRES_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final ImmutableList<TextualJMLConstruct>  simple_spec_body(
		ImmutableList<String> mods, Behavior b
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		TextualJMLSpecCase sc = new TextualJMLSpecCase(mods, b);
		result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(sc);
		
		
		{
		int _cnt64=0;
		_loop64:
		do {
			if ((_tokenSet_8.member(LA(1)))) {
				simple_spec_body_clause(sc, b);
			}
			else {
				if ( _cnt64>=1 ) { break _loop64; } else {throw new NoViableAltException(LT(1), getFilename());}
			}
			
			_cnt64++;
		} while (true);
		}
		return result;
	}
	
	public final ImmutableList<TextualJMLConstruct>  generic_spec_case_seq(
		ImmutableList<String> mods, Behavior b
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		ImmutableList<TextualJMLConstruct> result = null;
		
		
		ImmutableList<TextualJMLConstruct> list;
		
		
		result=generic_spec_case(mods, b);
		{
		_loop61:
		do {
			if ((LA(1)==ALSO||LA(1)==FOR_EXAMPLE||LA(1)==IMPLIES_THAT)) {
				{
				int _cnt60=0;
				_loop60:
				do {
					if ((LA(1)==ALSO||LA(1)==FOR_EXAMPLE||LA(1)==IMPLIES_THAT)) {
						also_keyword();
					}
					else {
						if ( _cnt60>=1 ) { break _loop60; } else {throw new NoViableAltException(LT(1), getFilename());}
					}
					
					_cnt60++;
				} while (true);
				}
				list=generic_spec_case(mods, b);
				if ( inputState.guessing==0 ) {
					
					result = result.append(list); 
					
				}
			}
			else {
				break _loop61;
			}
			
		} while (true);
		}
		return result;
	}
	
	public final void simple_spec_body_clause(
		TextualJMLSpecCase sc, Behavior b
	) throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		PositionedString ps;
		
		
		{
		switch ( LA(1)) {
		case ASSIGNABLE:
		case ASSIGNABLE_RED:
		case MODIFIABLE:
		case MODIFIABLE_RED:
		case MODIFIES:
		case MODIFIES_RED:
		{
			ps=assignable_clause();
			if ( inputState.guessing==0 ) {
				sc.addAssignable(ps);
			}
			break;
		}
		case ACCESSIBLE:
		case ACCESSIBLE_REDUNDANTLY:
		{
			ps=accessible_clause();
			if ( inputState.guessing==0 ) {
				sc.addAccessible(ps);
			}
			break;
		}
		case ENSURES:
		case ENSURES_RED:
		{
			ps=ensures_clause();
			if ( inputState.guessing==0 ) {
				sc.addEnsures(ps);
			}
			break;
		}
		case SIGNALS:
		case SIGNALS_RED:
		case EXSURES:
		case EXSURES_RED:
		{
			ps=signals_clause();
			if ( inputState.guessing==0 ) {
				sc.addSignals(ps);
			}
			break;
		}
		case SIGNALS_ONLY:
		case SIGNALS_ONLY_RED:
		{
			ps=signals_only_clause();
			if ( inputState.guessing==0 ) {
				sc.addSignalsOnly(ps);
			}
			break;
		}
		case DIVERGES:
		case DIVERGES_RED:
		{
			ps=diverges_clause();
			if ( inputState.guessing==0 ) {
				sc.addDiverges(ps);
			}
			break;
		}
		case MEASURED_BY:
		case MEASURED_BY_REDUNDANTLY:
		{
			ps=measured_by_clause();
			if ( inputState.guessing==0 ) {
				sc.addMeasuredBy(ps);
			}
			break;
		}
		case SPEC_NAME:
		{
			ps=name_clause();
			if ( inputState.guessing==0 ) {
				sc.addName(ps);
			}
			break;
		}
		case CAPTURES:
		case CAPTURES_RED:
		{
			captures_clause();
			break;
		}
		case WHEN:
		case WHEN_RED:
		{
			when_clause();
			break;
		}
		case WORKING_SPACE:
		case WORKING_SPACE_RED:
		{
			working_space_clause();
			break;
		}
		case DURATION:
		case DURATION_RED:
		{
			duration_clause();
			break;
		}
		case BREAKS:
		{
			ps=breaks_clause();
			if ( inputState.guessing==0 ) {
				sc.addBreaks(ps);
			}
			break;
		}
		case CONTINUES:
		{
			ps=continues_clause();
			if ( inputState.guessing==0 ) {
				sc.addContinues(ps);
			}
			break;
		}
		case RETURNS:
		{
			ps=returns_clause();
			if ( inputState.guessing==0 ) {
				sc.addReturns(ps);
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
			
				if(b == Behavior.EXCEPTIONAL_BEHAVIOR 
				   && !sc.getEnsures().isEmpty()) {
				    raiseError("ensures not allowed in exceptional behavior.");
				} else if(b == Behavior.NORMAL_BEHAVIOR 
				          && !sc.getSignals().isEmpty()) {
				    raiseError("signals not allowed in normal behavior.");
				} else if(b == Behavior.NORMAL_BEHAVIOR 
				          && !sc.getSignalsOnly().isEmpty()) {
				        raiseError("signals_only not allowed in normal behavior.");
				} else if(b == Behavior.NORMAL_BEHAVIOR 
				              && !sc.getBreaks().isEmpty()) {
					    raiseError("breaks not allowed in normal behavior.");
				} else if(b == Behavior.NORMAL_BEHAVIOR 
				              && !sc.getContinues().isEmpty()) {
					    raiseError("continues not allowed in normal behavior.");
					} else if(b == Behavior.NORMAL_BEHAVIOR 
				              && !sc.getReturns().isEmpty()) {
					    raiseError("returns not allowed in normal behavior.");
				    }
			
		}
	}
	
	public final PositionedString  assignable_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		assignable_keyword();
		result=expression();
		if ( inputState.guessing==0 ) {
			result = flipHeaps("assignable", result);
		}
		return result;
	}
	
	public final PositionedString  accessible_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		accessible_keyword();
		result=expression();
		if ( inputState.guessing==0 ) {
			result = result.prepend("accessible ");
		}
		return result;
	}
	
	public final PositionedString  ensures_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		ensures_keyword();
		result=expression();
		if ( inputState.guessing==0 ) {
			result = flipHeaps("ensures", result);
		}
		return result;
	}
	
	public final PositionedString  signals_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		signals_keyword();
		result=expression();
		if ( inputState.guessing==0 ) {
			result = result.prepend("signals ");
		}
		return result;
	}
	
	public final PositionedString  signals_only_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		signals_only_keyword();
		result=expression();
		if ( inputState.guessing==0 ) {
			result = result.prepend("signals_only ");
		}
		return result;
	}
	
	public final PositionedString  diverges_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		diverges_keyword();
		result=expression();
		return result;
	}
	
	public final PositionedString  measured_by_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		measured_by_keyword();
		result=expression();
		return result;
	}
	
	public final PositionedString  name_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		Token  spec = null;
		Token  name = null;
		
		spec = LT(1);
		match(SPEC_NAME);
		name = LT(1);
		match(STRING_LITERAL);
		match(SEMICOLON);
		if ( inputState.guessing==0 ) {
			
				result=createPositionedString(name.getText(), spec);
			
		}
		return result;
	}
	
	public final void captures_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		PositionedString ps;
		
		
		captures_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("captures clauses");
			
		}
	}
	
	public final void when_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		PositionedString ps;
		
		
		when_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("when clauses");
			
		}
	}
	
	public final void working_space_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		PositionedString ps;
		
		
		working_space_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("working_space clauses");
			
		}
	}
	
	public final void duration_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		PositionedString ps;
		
		
		duration_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("duration clauses");
			
		}
	}
	
	public final PositionedString  breaks_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		breaks_keyword();
		result=expression();
		if ( inputState.guessing==0 ) {
			result = result.prepend("breaks ");
		}
		return result;
	}
	
	public final PositionedString  continues_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		continues_keyword();
		result=expression();
		if ( inputState.guessing==0 ) {
			result = result.prepend("continues ");
		}
		return result;
	}
	
	public final PositionedString  returns_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		PositionedString result = null;
		
		
		returns_keyword();
		result=expression();
		if ( inputState.guessing==0 ) {
			result = result.prepend("returns ");
		}
		return result;
	}
	
	public final void assignable_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case ASSIGNABLE:
		{
			match(ASSIGNABLE);
			break;
		}
		case ASSIGNABLE_RED:
		{
			match(ASSIGNABLE_RED);
			break;
		}
		case MODIFIABLE:
		{
			match(MODIFIABLE);
			break;
		}
		case MODIFIABLE_RED:
		{
			match(MODIFIABLE_RED);
			break;
		}
		case MODIFIES:
		{
			match(MODIFIES);
			break;
		}
		case MODIFIES_RED:
		{
			match(MODIFIES_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void accessible_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case ACCESSIBLE:
		{
			match(ACCESSIBLE);
			break;
		}
		case ACCESSIBLE_REDUNDANTLY:
		{
			match(ACCESSIBLE_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void measured_by_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case MEASURED_BY:
		{
			match(MEASURED_BY);
			break;
		}
		case MEASURED_BY_REDUNDANTLY:
		{
			match(MEASURED_BY_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void ensures_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case ENSURES:
		{
			match(ENSURES);
			break;
		}
		case ENSURES_RED:
		{
			match(ENSURES_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void signals_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case SIGNALS:
		{
			match(SIGNALS);
			break;
		}
		case SIGNALS_RED:
		{
			match(SIGNALS_RED);
			break;
		}
		case EXSURES:
		{
			match(EXSURES);
			break;
		}
		case EXSURES_RED:
		{
			match(EXSURES_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void signals_only_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case SIGNALS_ONLY:
		{
			match(SIGNALS_ONLY);
			break;
		}
		case SIGNALS_ONLY_RED:
		{
			match(SIGNALS_ONLY_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void diverges_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case DIVERGES:
		{
			match(DIVERGES);
			break;
		}
		case DIVERGES_RED:
		{
			match(DIVERGES_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void captures_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case CAPTURES:
		{
			match(CAPTURES);
			break;
		}
		case CAPTURES_RED:
		{
			match(CAPTURES_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void when_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case WHEN:
		{
			match(WHEN);
			break;
		}
		case WHEN_RED:
		{
			match(WHEN_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void working_space_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case WORKING_SPACE:
		{
			match(WORKING_SPACE);
			break;
		}
		case WORKING_SPACE_RED:
		{
			match(WORKING_SPACE_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void duration_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case DURATION:
		{
			match(DURATION);
			break;
		}
		case DURATION_RED:
		{
			match(DURATION_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void represents_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case REPRESENTS:
		{
			match(REPRESENTS);
			break;
		}
		case REPRESENTS_RED:
		{
			match(REPRESENTS_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void constraint_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case CONSTRAINT:
		{
			match(CONSTRAINT);
			break;
		}
		case CONSTRAINT_RED:
		{
			match(CONSTRAINT_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void in_group_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		PositionedString ps;
		
		
		in_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("in-group clauses");
			
		}
	}
	
	public final void maps_into_clause() throws RecognitionException, TokenStreamException, SLTranslationException {
		
		
		PositionedString ps;
		
		
		maps_keyword();
		ps=expression();
		if ( inputState.guessing==0 ) {
			
				raiseNotSupported("maps-into clauses");
			
		}
	}
	
	public final void in_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case IN:
		{
			match(IN);
			break;
		}
		case IN_RED:
		{
			match(IN_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void maps_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case MAPS:
		{
			match(MAPS);
			break;
		}
		case MAPS_RED:
		{
			match(MAPS_RED);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final PositionedString  loop_invariant() throws RecognitionException, TokenStreamException {
		PositionedString result = null;
		
		
		maintaining_keyword();
		result=expression();
		if ( inputState.guessing==0 ) {
			result = flipHeaps("", result);
		}
		return result;
	}
	
	public final PositionedString  variant_function() throws RecognitionException, TokenStreamException {
		PositionedString result = null;
		
		
		decreasing_keyword();
		result=expression();
		return result;
	}
	
	public final void maintaining_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case MAINTAINING:
		{
			match(MAINTAINING);
			break;
		}
		case MAINTAINING_REDUNDANTLY:
		{
			match(MAINTAINING_REDUNDANTLY);
			break;
		}
		case LOOP_INVARIANT:
		{
			match(LOOP_INVARIANT);
			break;
		}
		case LOOP_INVARIANT_REDUNDANTLY:
		{
			match(LOOP_INVARIANT_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void decreasing_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case DECREASING:
		{
			match(DECREASING);
			break;
		}
		case DECREASING_REDUNDANTLY:
		{
			match(DECREASING_REDUNDANTLY);
			break;
		}
		case DECREASES:
		{
			match(DECREASES);
			break;
		}
		case DECREASES_REDUNDANTLY:
		{
			match(DECREASES_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void assume_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case ASSUME:
		{
			match(ASSUME);
			break;
		}
		case ASSUME_REDUNDANTLY:
		{
			match(ASSUME_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void assert_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case ASSERT:
		{
			match(ASSERT);
			break;
		}
		case ASSERT_REDUNDANTLY:
		{
			match(ASSERT_REDUNDANTLY);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void breaks_keyword() throws RecognitionException, TokenStreamException {
		
		
		match(BREAKS);
	}
	
	public final void continues_keyword() throws RecognitionException, TokenStreamException {
		
		
		match(CONTINUES);
	}
	
	public final void returns_keyword() throws RecognitionException, TokenStreamException {
		
		
		match(RETURNS);
	}
	
	public final void break_behavior_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case BREAK_BEHAVIOR:
		{
			match(BREAK_BEHAVIOR);
			break;
		}
		case BREAK_BEHAVIOUR:
		{
			match(BREAK_BEHAVIOUR);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void continue_behavior_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case CONTINUE_BEHAVIOR:
		{
			match(CONTINUE_BEHAVIOR);
			break;
		}
		case CONTINUE_BEHAVIOUR:
		{
			match(CONTINUE_BEHAVIOUR);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	public final void return_behavior_keyword() throws RecognitionException, TokenStreamException {
		
		
		switch ( LA(1)) {
		case RETURN_BEHAVIOR:
		{
			match(RETURN_BEHAVIOR);
			break;
		}
		case RETURN_BEHAVIOUR:
		{
			match(RETURN_BEHAVIOUR);
			break;
		}
		default:
		{
			throw new NoViableAltException(LT(1), getFilename());
		}
		}
	}
	
	
	public static final String[] _tokenNames = {
		"<0>",
		"EOF",
		"<2>",
		"NULL_TREE_LOOKAHEAD",
		"\"abstract\"",
		"\"accessible\"",
		"\"accessible_redundantly\"",
		"\"also\"",
		"\"assert\"",
		"\"assert_redundantly\"",
		"\"assume\"",
		"\"assume_redundantly\"",
		"\"assignable\"",
		"\"assignable_redundantly\"",
		"\"axiom\"",
		"\"behavior\"",
		"\"behaviour\"",
		"\"breaks\"",
		"\"break_behavior\"",
		"\"break_behaviour\"",
		"\"captures\"",
		"\"captures_redundantly\"",
		"\"code\"",
		"\"code_bigint_math\"",
		"\"code_java_math\"",
		"\"code_safe_math\"",
		"\"const\"",
		"\"constraint\"",
		"\"constraint_redundantly\"",
		"\"continues\"",
		"\"continue_behavior\"",
		"\"continue_behaviour\"",
		"\"decreases\"",
		"\"decreases_redundantly\"",
		"\"decreasing\"",
		"\"decreasing_redundantly\"",
		"\"diverges\"",
		"\"diverges_redundantly\"",
		"\"duration\"",
		"\"duration_redundantly\"",
		"\"ensures\"",
		"\"ensures_redundantly\"",
		"\"exceptional_behavior\"",
		"\"exceptional_behaviour\"",
		"\"extract\"",
		"\"final\"",
		"\"for_example\"",
		"\"forall\"",
		"\"ghost\"",
		"\"helper\"",
		"\"implies_that\"",
		"\"in\"",
		"\"in_redundantly\"",
		"\"initially\"",
		"\"instance\"",
		"\"invariant\"",
		"\"invariant_redundantly\"",
		"\"loop_invariant\"",
		"\"loop_invariant_redundantly\"",
		"\"maintaining\"",
		"\"maintaining_redundantly\"",
		"\"maps\"",
		"\"maps_redundantly\"",
		"\"measured_by\"",
		"\"measured_by_redundantly\"",
		"\"model\"",
		"\"modifiable\"",
		"\"modifiable_redundantly\"",
		"\"modifies\"",
		"\"modifies_redundantly\"",
		"\"monitored\"",
		"\"monitors_for\"",
		"\"native\"",
		"\"non_null\"",
		"\"normal_behavior\"",
		"\"normal_behaviour\"",
		"\"nowarn\"",
		"\"nullable\"",
		"\"nullable_by_default\"",
		"\"old\"",
		"\"private\"",
		"\"protected\"",
		"\"public\"",
		"\"pure\"",
		"\"strictly_pure\"",
		"\"readable\"",
		"\"represents\"",
		"\"represents_redundantly\"",
		"\"requires\"",
		"\"requires_redundantly\"",
		"\"returns\"",
		"\"return_behavior\"",
		"\"return_behaviour\"",
		"\"scopeSafe\"",
		"\"arbitraryScope\"",
		"\"arbitraryScopeThis\"",
		"\"set\"",
		"\"signals\"",
		"\"signals_only\"",
		"\"signals_only_redundantly\"",
		"\"signals_redundantly\"",
		"\"spec_bigint_math\"",
		"\"spec_java_math\"",
		"\"spec_protected\"",
		"\"spec_public\"",
		"\"name\"",
		"\"spec_safe_math\"",
		"\"static\"",
		"\"strictfp\"",
		"\"synchronized\"",
		"\"transient\"",
		"\"uninitialized\"",
		"\"volatile\"",
		"\"when\"",
		"\"when_redundantly\"",
		"\"working_space\"",
		"\"working_space_redundantly\"",
		"\"working_space_single_iteration\"",
		"\"working_space_single_iteration_param\"",
		"\"working_space_single_iteration_local\"",
		"\"working_space_single_iteration_constructed\"",
		"\"working_space_single_iteration_reentrant\"",
		"\"working_space_constructed\"",
		"\"working_space_local\"",
		"\"working_space_caller\"",
		"\"working_space_reentrant\"",
		"\"writable\"",
		"a single-line non-specification comment",
		"a multi-line non-specification comment",
		"a parameter declaration",
		"a letter",
		"a digit",
		"white space",
		"an identifier",
		"a parameter list",
		"NEST_START",
		"NEST_END",
		"a method body",
		"an initialiser",
		"a semicolon",
		"a string in double quotes",
		"ESC",
		"EXPRESSION",
		"`['",
		"`]'",
		"EXSURES",
		"EXSURES_RED",
		"LOOP_INVARIANT_REDUNDANTLY"
	};
	
	private static final long[] mk_tokenSet_0() {
		long[] data = { -2161745477878415374L, 4620143045793283775L, 393376L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = { 18894007811702800L, 10445362520578L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = { -9203123495674859280L, 8457023056244287L, 393344L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	private static final long[] mk_tokenSet_3() {
		long[] data = { -7329626050688729104L, 8457027351215679L, 917664L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_3 = new BitSet(mk_tokenSet_3());
	private static final long[] mk_tokenSet_4() {
		long[] data = { 1873497444986126336L, 0L, 524288L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_4 = new BitSet(mk_tokenSet_4());
	private static final long[] mk_tokenSet_5() {
		long[] data = { 12288L, 60L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_5 = new BitSet(mk_tokenSet_5());
	private static final long[] mk_tokenSet_6() {
		long[] data = { -9223367706987581344L, 8446577240703037L, 393344L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_6 = new BitSet(mk_tokenSet_6());
	private static final long[] mk_tokenSet_7() {
		long[] data = { -288248032892289038L, 4620143045793283775L, 917920L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_7 = new BitSet(mk_tokenSet_7());
	private static final long[] mk_tokenSet_8() {
		long[] data = { -9223367706987581344L, 8446577240703037L, 393216L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_8 = new BitSet(mk_tokenSet_8());
	
	}
