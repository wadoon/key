// $ANTLR 2.7.7 (2006-11-01): "jmlprelexer.g" -> "KeYJMLPreLexer.java"$

    package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.io.InputStream;
import antlr.TokenStreamException;
import antlr.TokenStreamIOException;
import antlr.TokenStreamRecognitionException;
import antlr.CharStreamException;
import antlr.CharStreamIOException;
import antlr.ANTLRException;
import java.io.Reader;
import java.util.Hashtable;
import antlr.CharScanner;
import antlr.InputBuffer;
import antlr.ByteBuffer;
import antlr.CharBuffer;
import antlr.Token;
import antlr.CommonToken;
import antlr.RecognitionException;
import antlr.NoViableAltForCharException;
import antlr.MismatchedCharException;
import antlr.TokenStream;
import antlr.ANTLRHashString;
import antlr.LexerSharedInputState;
import antlr.collections.impl.BitSet;
import antlr.SemanticException;

public class KeYJMLPreLexer extends antlr.CharScanner implements KeYJMLPreLexerTokenTypes, TokenStream
 {

    private boolean expressionMode = false;
    
    public void setExpressionMode(boolean b) {
    	expressionMode = b;
    }
public KeYJMLPreLexer(InputStream in) {
	this(new ByteBuffer(in));
}
public KeYJMLPreLexer(Reader in) {
	this(new CharBuffer(in));
}
public KeYJMLPreLexer(InputBuffer ib) {
	this(new LexerSharedInputState(ib));
}
public KeYJMLPreLexer(LexerSharedInputState state) {
	super(state);
	caseSensitiveLiterals = true;
	setCaseSensitive(true);
	literals = new Hashtable();
	literals.put(new ANTLRHashString("behavior", this), new Integer(15));
	literals.put(new ANTLRHashString("monitored", this), new Integer(70));
	literals.put(new ANTLRHashString("name", this), new Integer(105));
	literals.put(new ANTLRHashString("helper", this), new Integer(49));
	literals.put(new ANTLRHashString("accessible_redundantly", this), new Integer(6));
	literals.put(new ANTLRHashString("captures", this), new Integer(20));
	literals.put(new ANTLRHashString("constraint_redundantly", this), new Integer(28));
	literals.put(new ANTLRHashString("uninitialized", this), new Integer(111));
	literals.put(new ANTLRHashString("code_java_math", this), new Integer(24));
	literals.put(new ANTLRHashString("public", this), new Integer(82));
	literals.put(new ANTLRHashString("requires_redundantly", this), new Integer(89));
	literals.put(new ANTLRHashString("breaks", this), new Integer(17));
	literals.put(new ANTLRHashString("duration", this), new Integer(38));
	literals.put(new ANTLRHashString("break_behavior", this), new Integer(18));
	literals.put(new ANTLRHashString("non_null", this), new Integer(73));
	literals.put(new ANTLRHashString("loop_invariant", this), new Integer(57));
	literals.put(new ANTLRHashString("readable", this), new Integer(85));
	literals.put(new ANTLRHashString("code_safe_math", this), new Integer(25));
	literals.put(new ANTLRHashString("decreases_redundantly", this), new Integer(33));
	literals.put(new ANTLRHashString("initially", this), new Integer(53));
	literals.put(new ANTLRHashString("assignable", this), new Integer(12));
	literals.put(new ANTLRHashString("assert_redundantly", this), new Integer(9));
	literals.put(new ANTLRHashString("modifiable_redundantly", this), new Integer(67));
	literals.put(new ANTLRHashString("modifies", this), new Integer(68));
	literals.put(new ANTLRHashString("also", this), new Integer(7));
	literals.put(new ANTLRHashString("diverges", this), new Integer(36));
	literals.put(new ANTLRHashString("synchronized", this), new Integer(109));
	literals.put(new ANTLRHashString("nullable_by_default", this), new Integer(78));
	literals.put(new ANTLRHashString("const", this), new Integer(26));
	literals.put(new ANTLRHashString("code_bigint_math", this), new Integer(23));
	literals.put(new ANTLRHashString("pure", this), new Integer(83));
	literals.put(new ANTLRHashString("constraint", this), new Integer(27));
	literals.put(new ANTLRHashString("in_redundantly", this), new Integer(52));
	literals.put(new ANTLRHashString("returns", this), new Integer(90));
	literals.put(new ANTLRHashString("old", this), new Integer(79));
	literals.put(new ANTLRHashString("maintaining_redundantly", this), new Integer(60));
	literals.put(new ANTLRHashString("working_space_single_iteration_local", this), new Integer(119));
	literals.put(new ANTLRHashString("protected", this), new Integer(81));
	literals.put(new ANTLRHashString("spec_bigint_math", this), new Integer(101));
	literals.put(new ANTLRHashString("behaviour", this), new Integer(16));
	literals.put(new ANTLRHashString("normal_behavior", this), new Integer(74));
	literals.put(new ANTLRHashString("when", this), new Integer(113));
	literals.put(new ANTLRHashString("spec_public", this), new Integer(104));
	literals.put(new ANTLRHashString("strictfp", this), new Integer(108));
	literals.put(new ANTLRHashString("measured_by_redundantly", this), new Integer(64));
	literals.put(new ANTLRHashString("working_space", this), new Integer(115));
	literals.put(new ANTLRHashString("decreasing", this), new Integer(34));
	literals.put(new ANTLRHashString("spec_safe_math", this), new Integer(106));
	literals.put(new ANTLRHashString("represents", this), new Integer(86));
	literals.put(new ANTLRHashString("maintaining", this), new Integer(59));
	literals.put(new ANTLRHashString("arbitraryScope", this), new Integer(94));
	literals.put(new ANTLRHashString("exceptional_behavior", this), new Integer(42));
	literals.put(new ANTLRHashString("spec_protected", this), new Integer(103));
	literals.put(new ANTLRHashString("nullable", this), new Integer(77));
	literals.put(new ANTLRHashString("decreases", this), new Integer(32));
	literals.put(new ANTLRHashString("transient", this), new Integer(110));
	literals.put(new ANTLRHashString("set", this), new Integer(96));
	literals.put(new ANTLRHashString("ensures_redundantly", this), new Integer(41));
	literals.put(new ANTLRHashString("spec_java_math", this), new Integer(102));
	literals.put(new ANTLRHashString("native", this), new Integer(72));
	literals.put(new ANTLRHashString("model", this), new Integer(65));
	literals.put(new ANTLRHashString("arbitraryScopeThis", this), new Integer(95));
	literals.put(new ANTLRHashString("signals", this), new Integer(97));
	literals.put(new ANTLRHashString("working_space_single_iteration_param", this), new Integer(118));
	literals.put(new ANTLRHashString("ghost", this), new Integer(48));
	literals.put(new ANTLRHashString("continue_behavior", this), new Integer(30));
	literals.put(new ANTLRHashString("monitors_for", this), new Integer(71));
	literals.put(new ANTLRHashString("modifiable", this), new Integer(66));
	literals.put(new ANTLRHashString("working_space_caller", this), new Integer(124));
	literals.put(new ANTLRHashString("ensures", this), new Integer(40));
	literals.put(new ANTLRHashString("working_space_single_iteration_constructed", this), new Integer(120));
	literals.put(new ANTLRHashString("duration_redundantly", this), new Integer(39));
	literals.put(new ANTLRHashString("invariant", this), new Integer(55));
	literals.put(new ANTLRHashString("final", this), new Integer(45));
	literals.put(new ANTLRHashString("working_space_single_iteration", this), new Integer(117));
	literals.put(new ANTLRHashString("return_behaviour", this), new Integer(92));
	literals.put(new ANTLRHashString("invariant_redundantly", this), new Integer(56));
	literals.put(new ANTLRHashString("working_space_reentrant", this), new Integer(125));
	literals.put(new ANTLRHashString("forall", this), new Integer(47));
	literals.put(new ANTLRHashString("writable", this), new Integer(126));
	literals.put(new ANTLRHashString("working_space_local", this), new Integer(123));
	literals.put(new ANTLRHashString("volatile", this), new Integer(112));
	literals.put(new ANTLRHashString("assert", this), new Integer(8));
	literals.put(new ANTLRHashString("exceptional_behaviour", this), new Integer(43));
	literals.put(new ANTLRHashString("for_example", this), new Integer(46));
	literals.put(new ANTLRHashString("scopeSafe", this), new Integer(93));
	literals.put(new ANTLRHashString("break_behaviour", this), new Integer(19));
	literals.put(new ANTLRHashString("implies_that", this), new Integer(50));
	literals.put(new ANTLRHashString("represents_redundantly", this), new Integer(87));
	literals.put(new ANTLRHashString("extract", this), new Integer(44));
	literals.put(new ANTLRHashString("maps", this), new Integer(61));
	literals.put(new ANTLRHashString("continue_behaviour", this), new Integer(31));
	literals.put(new ANTLRHashString("normal_behaviour", this), new Integer(75));
	literals.put(new ANTLRHashString("continues", this), new Integer(29));
	literals.put(new ANTLRHashString("private", this), new Integer(80));
	literals.put(new ANTLRHashString("axiom", this), new Integer(14));
	literals.put(new ANTLRHashString("when_redundantly", this), new Integer(114));
	literals.put(new ANTLRHashString("requires", this), new Integer(88));
	literals.put(new ANTLRHashString("measured_by", this), new Integer(63));
	literals.put(new ANTLRHashString("code", this), new Integer(22));
	literals.put(new ANTLRHashString("working_space_redundantly", this), new Integer(116));
	literals.put(new ANTLRHashString("static", this), new Integer(107));
	literals.put(new ANTLRHashString("diverges_redundantly", this), new Integer(37));
	literals.put(new ANTLRHashString("loop_invariant_redundantly", this), new Integer(58));
	literals.put(new ANTLRHashString("abstract", this), new Integer(4));
	literals.put(new ANTLRHashString("nowarn", this), new Integer(76));
	literals.put(new ANTLRHashString("signals_only", this), new Integer(98));
	literals.put(new ANTLRHashString("modifies_redundantly", this), new Integer(69));
	literals.put(new ANTLRHashString("assume_redundantly", this), new Integer(11));
	literals.put(new ANTLRHashString("assume", this), new Integer(10));
	literals.put(new ANTLRHashString("instance", this), new Integer(54));
	literals.put(new ANTLRHashString("signals_redundantly", this), new Integer(100));
	literals.put(new ANTLRHashString("working_space_constructed", this), new Integer(122));
	literals.put(new ANTLRHashString("strictly_pure", this), new Integer(84));
	literals.put(new ANTLRHashString("decreasing_redundantly", this), new Integer(35));
	literals.put(new ANTLRHashString("signals_only_redundantly", this), new Integer(99));
	literals.put(new ANTLRHashString("working_space_single_iteration_reentrant", this), new Integer(121));
	literals.put(new ANTLRHashString("accessible", this), new Integer(5));
	literals.put(new ANTLRHashString("captures_redundantly", this), new Integer(21));
	literals.put(new ANTLRHashString("in", this), new Integer(51));
	literals.put(new ANTLRHashString("assignable_redundantly", this), new Integer(13));
	literals.put(new ANTLRHashString("return_behavior", this), new Integer(91));
	literals.put(new ANTLRHashString("maps_redundantly", this), new Integer(62));
}

public Token nextToken() throws TokenStreamException {
	Token theRetToken=null;
tryAgain:
	for (;;) {
		Token _token = null;
		int _ttype = Token.INVALID_TYPE;
		resetText();
		try {   // for char stream error handling
			try {   // for lexical error handling
				if (((LA(1)=='(') && (_tokenSet_0.member(LA(2))))&&(!expressionMode)) {
					mPARAM_LIST(true);
					theRetToken=_returnToken;
				}
				else if (((LA(1)=='{') && (LA(2)=='|'))&&(!expressionMode)) {
					mNEST_START(true);
					theRetToken=_returnToken;
				}
				else if (((LA(1)=='|') && (LA(2)=='}'))&&(!expressionMode)) {
					mNEST_END(true);
					theRetToken=_returnToken;
				}
				else if (((LA(1)=='{') && ((LA(2) >= '\u0003' && LA(2) <= '\ufffe')))&&(!expressionMode)) {
					mBODY(true);
					theRetToken=_returnToken;
				}
				else if (((LA(1)=='=') && ((LA(2) >= '\u0003' && LA(2) <= '\ufffe')))&&(!expressionMode)) {
					mINITIALISER(true);
					theRetToken=_returnToken;
				}
				else if ((LA(1)=='"') && ((LA(2) >= '\u0003' && LA(2) <= '\ufffe'))) {
					mSTRING_LITERAL(true);
					theRetToken=_returnToken;
				}
				else if (((_tokenSet_1.member(LA(1))) && (true))&&(!expressionMode)) {
					mWS(true);
					theRetToken=_returnToken;
				}
				else if (((_tokenSet_2.member(LA(1))) && (true))&&(!expressionMode)) {
					mIDENT(true);
					theRetToken=_returnToken;
				}
				else if ((((LA(1) >= '\u0003' && LA(1) <= '\ufffe')) && (true))&&(expressionMode)) {
					mEXPRESSION(true);
					theRetToken=_returnToken;
				}
				else if (((LA(1)==';') && (true))&&(!expressionMode)) {
					mSEMICOLON(true);
					theRetToken=_returnToken;
				}
				else if ((LA(1)=='[') && (true)) {
					mAXIOM_NAME_BEGIN(true);
					theRetToken=_returnToken;
				}
				else if ((LA(1)==']') && (true)) {
					mAXIOM_NAME_END(true);
					theRetToken=_returnToken;
				}
				else {
					if (LA(1)==EOF_CHAR) {uponEOF(); _returnToken = makeToken(Token.EOF_TYPE);}
				else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				
				if ( _returnToken==null ) continue tryAgain; // found SKIP token
				_ttype = _returnToken.getType();
				_ttype = testLiteralsTable(_ttype);
				_returnToken.setType(_ttype);
				return _returnToken;
			}
			catch (RecognitionException e) {
				throw new TokenStreamRecognitionException(e);
			}
		}
		catch (CharStreamException cse) {
			if ( cse instanceof CharStreamIOException ) {
				throw new TokenStreamIOException(((CharStreamIOException)cse).io);
			}
			else {
				throw new TokenStreamException(cse.getMessage());
			}
		}
	}
}

	protected final void mSL_COMMENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SL_COMMENT;
		int _saveIndex;
		
		match("//");
		{
		boolean synPredMatched5 = false;
		if (((_tokenSet_3.member(LA(1))) && (true))) {
			int _m5 = mark();
			synPredMatched5 = true;
			inputState.guessing++;
			try {
				{
				{
				match(_tokenSet_3);
				}
				}
			}
			catch (RecognitionException pe) {
				synPredMatched5 = false;
			}
			rewind(_m5);
inputState.guessing--;
		}
		if ( synPredMatched5 ) {
			{
			match(_tokenSet_3);
			}
			{
			_loop8:
			do {
				if ((_tokenSet_4.member(LA(1))) && (true)) {
					matchNot('\n');
				}
				else {
					break _loop8;
				}
				
			} while (true);
			}
		}
		else {
		}
		
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mML_COMMENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ML_COMMENT;
		int _saveIndex;
		
		match("/*");
		{
		boolean synPredMatched13 = false;
		if (((_tokenSet_5.member(LA(1))) && ((LA(2) >= '\u0003' && LA(2) <= '\ufffe')))) {
			int _m13 = mark();
			synPredMatched13 = true;
			inputState.guessing++;
			try {
				{
				if ((_tokenSet_6.member(LA(1)))) {
					{
					match(_tokenSet_6);
					}
					matchNot(EOF_CHAR);
				}
				else if ((LA(1)=='*')) {
					match('*');
					matchNot('/');
				}
				else {
					throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
				}
				
				}
			}
			catch (RecognitionException pe) {
				synPredMatched13 = false;
			}
			rewind(_m13);
inputState.guessing--;
		}
		if ( synPredMatched13 ) {
			{
			if ((LA(1)=='\n')) {
				match('\n');
				if ( inputState.guessing==0 ) {
					newline();
				}
			}
			else if ((_tokenSet_3.member(LA(1)))) {
				matchNot('@');
			}
			else {
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			
			}
			{
			_loop16:
			do {
				// nongreedy exit test
				if ((LA(1)=='*') && (LA(2)=='/')) break _loop16;
				if ((_tokenSet_4.member(LA(1))) && ((LA(2) >= '\u0003' && LA(2) <= '\ufffe'))) {
					matchNot('\n');
				}
				else if ((LA(1)=='\n')) {
					match('\n');
					if ( inputState.guessing==0 ) {
						newline();
					}
				}
				else {
					break _loop16;
				}
				
			} while (true);
			}
		}
		else if ((LA(1)=='*') && (LA(2)=='/')) {
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		
		}
		match("*/");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mPARAM_DECL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PARAM_DECL;
		int _saveIndex;
		
		{
		boolean synPredMatched22 = false;
		if (((LA(1)=='n') && (LA(2)=='o'||LA(2)=='u'))) {
			int _m22 = mark();
			synPredMatched22 = true;
			inputState.guessing++;
			try {
				{
				if ((LA(1)=='n') && (LA(2)=='o')) {
					match("non_null");
					{
					if ((_tokenSet_1.member(LA(1)))) {
						_saveIndex=text.length();
						mWS(false);
						text.setLength(_saveIndex);
					}
					else {
					}
					
					}
				}
				else if ((LA(1)=='n') && (LA(2)=='u')) {
					match("nullable");
					{
					if ((_tokenSet_1.member(LA(1)))) {
						_saveIndex=text.length();
						mWS(false);
						text.setLength(_saveIndex);
					}
					else {
					}
					
					}
				}
				else {
					throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
				}
				
				}
			}
			catch (RecognitionException pe) {
				synPredMatched22 = false;
			}
			rewind(_m22);
inputState.guessing--;
		}
		if ( synPredMatched22 ) {
			if ( inputState.guessing==0 ) {
				
					    text.append("/*@");
					
			}
			{
			if ((LA(1)=='n') && (LA(2)=='o')) {
				match("non_null");
				{
				switch ( LA(1)) {
				case '\t':  case '\n':  case '\r':  case ' ':
				case '*':  case '/':  case '@':
				{
					_saveIndex=text.length();
					mWS(false);
					text.setLength(_saveIndex);
					break;
				}
				case '$':  case 'A':  case 'B':  case 'C':
				case 'D':  case 'E':  case 'F':  case 'G':
				case 'H':  case 'I':  case 'J':  case 'K':
				case 'L':  case 'M':  case 'N':  case 'O':
				case 'P':  case 'Q':  case 'R':  case 'S':
				case 'T':  case 'U':  case 'V':  case 'W':
				case 'X':  case 'Y':  case 'Z':  case '\\':
				case '_':  case 'a':  case 'b':  case 'c':
				case 'd':  case 'e':  case 'f':  case 'g':
				case 'h':  case 'i':  case 'j':  case 'k':
				case 'l':  case 'm':  case 'n':  case 'o':
				case 'p':  case 'q':  case 'r':  case 's':
				case 't':  case 'u':  case 'v':  case 'w':
				case 'x':  case 'y':  case 'z':
				{
					break;
				}
				default:
				{
					throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
				}
				}
				}
			}
			else if ((LA(1)=='n') && (LA(2)=='u')) {
				match("nullable");
				{
				switch ( LA(1)) {
				case '\t':  case '\n':  case '\r':  case ' ':
				case '*':  case '/':  case '@':
				{
					_saveIndex=text.length();
					mWS(false);
					text.setLength(_saveIndex);
					break;
				}
				case '$':  case 'A':  case 'B':  case 'C':
				case 'D':  case 'E':  case 'F':  case 'G':
				case 'H':  case 'I':  case 'J':  case 'K':
				case 'L':  case 'M':  case 'N':  case 'O':
				case 'P':  case 'Q':  case 'R':  case 'S':
				case 'T':  case 'U':  case 'V':  case 'W':
				case 'X':  case 'Y':  case 'Z':  case '\\':
				case '_':  case 'a':  case 'b':  case 'c':
				case 'd':  case 'e':  case 'f':  case 'g':
				case 'h':  case 'i':  case 'j':  case 'k':
				case 'l':  case 'm':  case 'n':  case 'o':
				case 'p':  case 'q':  case 'r':  case 's':
				case 't':  case 'u':  case 'v':  case 'w':
				case 'x':  case 'y':  case 'z':
				{
					break;
				}
				default:
				{
					throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
				}
				}
				}
			}
			else {
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			
			}
			if ( inputState.guessing==0 ) {
				
					    text.append("@*/");
				
			}
		}
		else if ((_tokenSet_2.member(LA(1))) && (_tokenSet_7.member(LA(2)))) {
		}
		else {
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		
		}
		mIDENT(false);
		{
		switch ( LA(1)) {
		case '\t':  case '\n':  case '\r':  case ' ':
		case '*':  case '/':  case '@':
		{
			_saveIndex=text.length();
			mWS(false);
			text.setLength(_saveIndex);
			break;
		}
		case '$':  case 'A':  case 'B':  case 'C':
		case 'D':  case 'E':  case 'F':  case 'G':
		case 'H':  case 'I':  case 'J':  case 'K':
		case 'L':  case 'M':  case 'N':  case 'O':
		case 'P':  case 'Q':  case 'R':  case 'S':
		case 'T':  case 'U':  case 'V':  case 'W':
		case 'X':  case 'Y':  case 'Z':  case '\\':
		case '_':  case 'a':  case 'b':  case 'c':
		case 'd':  case 'e':  case 'f':  case 'g':
		case 'h':  case 'i':  case 'j':  case 'k':
		case 'l':  case 'm':  case 'n':  case 'o':
		case 'p':  case 'q':  case 'r':  case 's':
		case 't':  case 'u':  case 'v':  case 'w':
		case 'x':  case 'y':  case 'z':
		{
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		if ( inputState.guessing==0 ) {
			text.append(" ");
		}
		mIDENT(false);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mWS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = WS;
		int _saveIndex;
		
		boolean acceptAt = false;
		
		
		if (!(!expressionMode))
		  throw new SemanticException("!expressionMode");
		{
		int _cnt35=0;
		_loop35:
		do {
			switch ( LA(1)) {
			case ' ':
			{
				match(' ');
				break;
			}
			case '\t':
			{
				match('\t');
				break;
			}
			case '\n':
			{
				match('\n');
				if ( inputState.guessing==0 ) {
					newline(); acceptAt = true;
				}
				break;
			}
			case '\r':
			{
				match('\r');
				break;
			}
			case '*':
			{
				match("*/");
				break;
			}
			default:
				boolean synPredMatched32 = false;
				if (((LA(1)=='/') && (LA(2)=='/'))) {
					int _m32 = mark();
					synPredMatched32 = true;
					inputState.guessing++;
					try {
						{
						match("//@");
						}
					}
					catch (RecognitionException pe) {
						synPredMatched32 = false;
					}
					rewind(_m32);
inputState.guessing--;
				}
				if ( synPredMatched32 ) {
					match("//@");
				}
				else {
					boolean synPredMatched34 = false;
					if (((LA(1)=='/') && (LA(2)=='*'))) {
						int _m34 = mark();
						synPredMatched34 = true;
						inputState.guessing++;
						try {
							{
							match("/*@");
							}
						}
						catch (RecognitionException pe) {
							synPredMatched34 = false;
						}
						rewind(_m34);
inputState.guessing--;
					}
					if ( synPredMatched34 ) {
						match("/*@");
					}
					else if ((LA(1)=='@') && (LA(2)=='*')) {
						match("@*/");
					}
					else if ((LA(1)=='/') && (LA(2)=='/')) {
						mSL_COMMENT(false);
					}
					else if ((LA(1)=='/') && (LA(2)=='*')) {
						mML_COMMENT(false);
					}
					else if (((LA(1)=='@') && (true))&&(acceptAt)) {
						match('@');
					}
				else {
					if ( _cnt35>=1 ) { break _loop35; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				}}
				_cnt35++;
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
					_ttype = Token.SKIP; 
				
			}
			if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
				_token = makeToken(_ttype);
				_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
			}
			_returnToken = _token;
		}
		
	public final void mIDENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = IDENT;
		int _saveIndex;
		
		if (!(!expressionMode))
		  throw new SemanticException("!expressionMode");
		mLETTER(false);
		{
		_loop38:
		do {
			switch ( LA(1)) {
			case '0':  case '1':  case '2':  case '3':
			case '4':  case '5':  case '6':  case '7':
			case '8':  case '9':
			{
				mDIGIT(false);
				break;
			}
			case '[':
			{
				match("[]");
				break;
			}
			case '.':
			{
				match('.');
				break;
			}
			default:
				if ((_tokenSet_2.member(LA(1))) && (true)) {
					mLETTER(false);
				}
			else {
				break _loop38;
			}
			}
		} while (true);
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mLETTER(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LETTER;
		int _saveIndex;
		
		switch ( LA(1)) {
		case 'a':  case 'b':  case 'c':  case 'd':
		case 'e':  case 'f':  case 'g':  case 'h':
		case 'i':  case 'j':  case 'k':  case 'l':
		case 'm':  case 'n':  case 'o':  case 'p':
		case 'q':  case 'r':  case 's':  case 't':
		case 'u':  case 'v':  case 'w':  case 'x':
		case 'y':  case 'z':
		{
			matchRange('a','z');
			break;
		}
		case 'A':  case 'B':  case 'C':  case 'D':
		case 'E':  case 'F':  case 'G':  case 'H':
		case 'I':  case 'J':  case 'K':  case 'L':
		case 'M':  case 'N':  case 'O':  case 'P':
		case 'Q':  case 'R':  case 'S':  case 'T':
		case 'U':  case 'V':  case 'W':  case 'X':
		case 'Y':  case 'Z':
		{
			matchRange('A','Z');
			break;
		}
		case '_':
		{
			match('_');
			break;
		}
		case '$':
		{
			match('$');
			break;
		}
		case '\\':
		{
			match('\\');
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mDIGIT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DIGIT;
		int _saveIndex;
		
		matchRange('0','9');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mPARAM_LIST(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PARAM_LIST;
		int _saveIndex;
		
		if (!(!expressionMode))
		  throw new SemanticException("!expressionMode");
		match('(');
		{
		switch ( LA(1)) {
		case '\t':  case '\n':  case '\r':  case ' ':
		case '*':  case '/':  case '@':
		{
			_saveIndex=text.length();
			mWS(false);
			text.setLength(_saveIndex);
			break;
		}
		case '$':  case ')':  case 'A':  case 'B':
		case 'C':  case 'D':  case 'E':  case 'F':
		case 'G':  case 'H':  case 'I':  case 'J':
		case 'K':  case 'L':  case 'M':  case 'N':
		case 'O':  case 'P':  case 'Q':  case 'R':
		case 'S':  case 'T':  case 'U':  case 'V':
		case 'W':  case 'X':  case 'Y':  case 'Z':
		case '\\':  case '_':  case 'a':  case 'b':
		case 'c':  case 'd':  case 'e':  case 'f':
		case 'g':  case 'h':  case 'i':  case 'j':
		case 'k':  case 'l':  case 'm':  case 'n':
		case 'o':  case 'p':  case 'q':  case 'r':
		case 's':  case 't':  case 'u':  case 'v':
		case 'w':  case 'x':  case 'y':  case 'z':
		{
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		{
		switch ( LA(1)) {
		case '$':  case 'A':  case 'B':  case 'C':
		case 'D':  case 'E':  case 'F':  case 'G':
		case 'H':  case 'I':  case 'J':  case 'K':
		case 'L':  case 'M':  case 'N':  case 'O':
		case 'P':  case 'Q':  case 'R':  case 'S':
		case 'T':  case 'U':  case 'V':  case 'W':
		case 'X':  case 'Y':  case 'Z':  case '\\':
		case '_':  case 'a':  case 'b':  case 'c':
		case 'd':  case 'e':  case 'f':  case 'g':
		case 'h':  case 'i':  case 'j':  case 'k':
		case 'l':  case 'm':  case 'n':  case 'o':
		case 'p':  case 'q':  case 'r':  case 's':
		case 't':  case 'u':  case 'v':  case 'w':
		case 'x':  case 'y':  case 'z':
		{
			mPARAM_DECL(false);
			{
			switch ( LA(1)) {
			case '\t':  case '\n':  case '\r':  case ' ':
			case '*':  case '/':  case '@':
			{
				_saveIndex=text.length();
				mWS(false);
				text.setLength(_saveIndex);
				break;
			}
			case ')':  case ',':
			{
				break;
			}
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			{
			_loop46:
			do {
				if ((LA(1)==',')) {
					match(',');
					{
					switch ( LA(1)) {
					case '\t':  case '\n':  case '\r':  case ' ':
					case '*':  case '/':  case '@':
					{
						_saveIndex=text.length();
						mWS(false);
						text.setLength(_saveIndex);
						break;
					}
					case '$':  case 'A':  case 'B':  case 'C':
					case 'D':  case 'E':  case 'F':  case 'G':
					case 'H':  case 'I':  case 'J':  case 'K':
					case 'L':  case 'M':  case 'N':  case 'O':
					case 'P':  case 'Q':  case 'R':  case 'S':
					case 'T':  case 'U':  case 'V':  case 'W':
					case 'X':  case 'Y':  case 'Z':  case '\\':
					case '_':  case 'a':  case 'b':  case 'c':
					case 'd':  case 'e':  case 'f':  case 'g':
					case 'h':  case 'i':  case 'j':  case 'k':
					case 'l':  case 'm':  case 'n':  case 'o':
					case 'p':  case 'q':  case 'r':  case 's':
					case 't':  case 'u':  case 'v':  case 'w':
					case 'x':  case 'y':  case 'z':
					{
						break;
					}
					default:
					{
						throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
					}
					}
					}
					mPARAM_DECL(false);
					{
					switch ( LA(1)) {
					case '\t':  case '\n':  case '\r':  case ' ':
					case '*':  case '/':  case '@':
					{
						_saveIndex=text.length();
						mWS(false);
						text.setLength(_saveIndex);
						break;
					}
					case ')':  case ',':
					{
						break;
					}
					default:
					{
						throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
					}
					}
					}
				}
				else {
					break _loop46;
				}
				
			} while (true);
			}
			break;
		}
		case ')':
		{
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		match(')');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mNEST_START(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NEST_START;
		int _saveIndex;
		
		if (!(!expressionMode))
		  throw new SemanticException("!expressionMode");
		match("{|");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mNEST_END(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NEST_END;
		int _saveIndex;
		
		if (!(!expressionMode))
		  throw new SemanticException("!expressionMode");
		match("|}");
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mBODY(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = BODY;
		int _saveIndex;
		
		int braceCounter = 0;
		boolean ignoreAt = false;
		
		
		if (!(!expressionMode))
		  throw new SemanticException("!expressionMode");
		match('{');
		{
		_loop51:
		do {
			switch ( LA(1)) {
			case '{':
			{
				match('{');
				if ( inputState.guessing==0 ) {
					braceCounter++; ignoreAt = false;
				}
				break;
			}
			case '\n':
			{
				match('\n');
				if ( inputState.guessing==0 ) {
					newline(); ignoreAt = true;
				}
				break;
			}
			case ' ':
			{
				match(' ');
				break;
			}
			case '\u000c':
			{
				match('\u000C');
				break;
			}
			case '\t':
			{
				match('\t');
				break;
			}
			case '\r':
			{
				match('\r');
				break;
			}
			default:
				if (((LA(1)=='}') && ((LA(2) >= '\u0003' && LA(2) <= '\ufffe')))&&(braceCounter > 0)) {
					match('}');
					if ( inputState.guessing==0 ) {
						braceCounter--; ignoreAt = false;
					}
				}
				else if (((LA(1)=='@') && ((LA(2) >= '\u0003' && LA(2) <= '\ufffe')))&&(!ignoreAt)) {
					match('@');
				}
				else if (((LA(1)=='@') && ((LA(2) >= '\u0003' && LA(2) <= '\ufffe')))&&(ignoreAt)) {
					_saveIndex=text.length();
					match('@');
					text.setLength(_saveIndex);
					if ( inputState.guessing==0 ) {
						ignoreAt = false;
					}
				}
				else if ((_tokenSet_8.member(LA(1)))) {
					matchNot('}');
					if ( inputState.guessing==0 ) {
						ignoreAt = false;
					}
				}
			else {
				break _loop51;
			}
			}
		} while (true);
		}
		if (!(braceCounter == 0))
		  throw new SemanticException("braceCounter == 0");
		match('}');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mINITIALISER(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = INITIALISER;
		int _saveIndex;
		
		assert inputState.guessing == 0;
		
		
		if (!(!expressionMode))
		  throw new SemanticException("!expressionMode");
		{
		match('=');
		if ( inputState.guessing==0 ) {
			setExpressionMode(true);
		}
		mEXPRESSION(false);
		if ( inputState.guessing==0 ) {
			setExpressionMode(false);
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mEXPRESSION(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = EXPRESSION;
		int _saveIndex;
		
		int parenthesesCounter = 0;
		
		
		if (!(expressionMode))
		  throw new SemanticException("expressionMode");
		{
		_loop63:
		do {
			switch ( LA(1)) {
			case '(':
			{
				match('(');
				if ( inputState.guessing==0 ) {
					parenthesesCounter++;
				}
				break;
			}
			case ')':
			{
				match(')');
				if ( inputState.guessing==0 ) {
					parenthesesCounter--;
				}
				break;
			}
			case '\n':
			{
				match('\n');
				if ( inputState.guessing==0 ) {
					newline();
				}
				break;
			}
			default:
				if (((LA(1)==';') && ((LA(2) >= '\u0003' && LA(2) <= '\ufffe')))&&(parenthesesCounter > 0)) {
					match(';');
				}
				else if ((_tokenSet_9.member(LA(1)))) {
					matchNot(';');
				}
			else {
				break _loop63;
			}
			}
		} while (true);
		}
		if (!(parenthesesCounter == 0))
		  throw new SemanticException("parenthesesCounter == 0");
		match(';');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSEMICOLON(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SEMICOLON;
		int _saveIndex;
		
		if (!(!expressionMode))
		  throw new SemanticException("!expressionMode");
		match(';');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSTRING_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = STRING_LITERAL;
		int _saveIndex;
		
		_saveIndex=text.length();
		match('"');
		text.setLength(_saveIndex);
		{
		_loop58:
		do {
			if ((LA(1)=='\\')) {
				mESC(false);
			}
			else if ((_tokenSet_10.member(LA(1)))) {
				{
				match(_tokenSet_10);
				}
			}
			else {
				break _loop58;
			}
			
		} while (true);
		}
		_saveIndex=text.length();
		match('"');
		text.setLength(_saveIndex);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mESC(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ESC;
		int _saveIndex;
		
		match('\\');
		{
		switch ( LA(1)) {
		case 'n':
		{
			match('n');
			if ( inputState.guessing==0 ) {
				text.setLength(_begin); text.append("\n");
			}
			break;
		}
		case 'r':
		{
			match('r');
			if ( inputState.guessing==0 ) {
				text.setLength(_begin); text.append("\r");
			}
			break;
		}
		case 't':
		{
			match('t');
			if ( inputState.guessing==0 ) {
				text.setLength(_begin); text.append("\t");
			}
			break;
		}
		case 'b':
		{
			match('b');
			if ( inputState.guessing==0 ) {
				text.setLength(_begin); text.append("\b");
			}
			break;
		}
		case 'f':
		{
			match('f');
			if ( inputState.guessing==0 ) {
				text.setLength(_begin); text.append("\f");
			}
			break;
		}
		case '"':
		{
			match('"');
			if ( inputState.guessing==0 ) {
				text.setLength(_begin); text.append("\"");
			}
			break;
		}
		case '\'':
		{
			match('\'');
			if ( inputState.guessing==0 ) {
				text.setLength(_begin); text.append("'");
			}
			break;
		}
		case '\\':
		{
			match('\\');
			if ( inputState.guessing==0 ) {
				text.setLength(_begin); text.append("\\");
			}
			break;
		}
		case ':':
		{
			match(':');
			if ( inputState.guessing==0 ) {
				text.setLength(_begin); text.append("\\:");
			}
			break;
		}
		case ' ':
		{
			match(' ');
			if ( inputState.guessing==0 ) {
				text.setLength(_begin); text.append("\\ ");
			}
			break;
		}
		default:
		{
			throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
		}
		}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mAXIOM_NAME_BEGIN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = AXIOM_NAME_BEGIN;
		int _saveIndex;
		
		match('[');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mAXIOM_NAME_END(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = AXIOM_NAME_END;
		int _saveIndex;
		
		match(']');
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	
	private static final long[] mk_tokenSet_0() {
		long[] data = new long[1025];
		data[0]=147407572575744L;
		data[1]=576460746263625727L;
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = new long[1025];
		data[0]=145139829843456L;
		data[1]=1L;
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = new long[1025];
		data[0]=68719476736L;
		data[1]=576460746263625726L;
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	private static final long[] mk_tokenSet_3() {
		long[] data = new long[2048];
		data[0]=-1032L;
		data[1]=-2L;
		for (int i = 2; i<=1022; i++) { data[i]=-1L; }
		data[1023]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_3 = new BitSet(mk_tokenSet_3());
	private static final long[] mk_tokenSet_4() {
		long[] data = new long[2048];
		data[0]=-1032L;
		for (int i = 1; i<=1022; i++) { data[i]=-1L; }
		data[1023]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_4 = new BitSet(mk_tokenSet_4());
	private static final long[] mk_tokenSet_5() {
		long[] data = new long[2048];
		data[0]=-8L;
		data[1]=-2L;
		for (int i = 2; i<=1022; i++) { data[i]=-1L; }
		data[1023]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_5 = new BitSet(mk_tokenSet_5());
	private static final long[] mk_tokenSet_6() {
		long[] data = new long[2048];
		data[0]=-4398046511112L;
		for (int i = 1; i<=1022; i++) { data[i]=-1L; }
		data[1023]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_6 = new BitSet(mk_tokenSet_6());
	private static final long[] mk_tokenSet_7() {
		long[] data = new long[1025];
		data[0]=288164478468498944L;
		data[1]=576460746397843455L;
		return data;
	}
	public static final BitSet _tokenSet_7 = new BitSet(mk_tokenSet_7());
	private static final long[] mk_tokenSet_8() {
		long[] data = new long[2048];
		data[0]=-4294981128L;
		data[1]=-2882303761517117442L;
		for (int i = 2; i<=1022; i++) { data[i]=-1L; }
		data[1023]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_8 = new BitSet(mk_tokenSet_8());
	private static final long[] mk_tokenSet_9() {
		long[] data = new long[2048];
		data[0]=-576464050838307848L;
		for (int i = 1; i<=1022; i++) { data[i]=-1L; }
		data[1023]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_9 = new BitSet(mk_tokenSet_9());
	private static final long[] mk_tokenSet_10() {
		long[] data = new long[2048];
		data[0]=-17179869192L;
		data[1]=-268435457L;
		for (int i = 2; i<=1022; i++) { data[i]=-1L; }
		data[1023]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_10 = new BitSet(mk_tokenSet_10());
	
	}
