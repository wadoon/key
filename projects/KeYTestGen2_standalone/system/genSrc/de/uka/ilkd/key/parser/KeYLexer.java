// $ANTLR 2.7.7 (2006-11-01): "lexer.g" -> "KeYLexer.java"$

    package de.uka.ilkd.key.parser;

    import java.io.InputStream;
    import de.uka.ilkd.key.util.*;
    import java.util.HashMap;
    import antlr.TokenStreamSelector;
    import java.util.NoSuchElementException;
    import java.io.*;

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

/**
 * The common lexer for declarations, terms, formulae, Taclets, etc.
 */
public class KeYLexer extends antlr.CharScanner implements KeYLexerTokenTypes, TokenStream
 {

    protected KeYExceptionHandler keh = new KeYRecoderExcHandler();
    protected TokenStreamSelector selector;

    // why is keh sometimes null?

    public KeYLexer(InputStream in, KeYExceptionHandler keh){
        this(in);
	if(keh != null)
            this.keh = keh; 
	this.selector = new TokenStreamSelector();
	selector.select(this);
    }
    
    public KeYLexer(InputStream in, KeYExceptionHandler keh, 
                    TokenStreamSelector selector){
        this(in);
	if(keh != null)
          this.keh = keh; 
	this.selector = selector;
    }
    
    public KeYLexer(Reader in, KeYExceptionHandler keh) {
        this(new CharBuffer(in));
	if(keh != null)
          this.keh = keh; 
	this.selector = new TokenStreamSelector();
	selector.select(this);
    }

    public void reportError(RecognitionException ex){
        keh.reportException(ex);
    }
    
    public TokenStreamSelector getSelector() {
      return selector;
    }

    public void uponEOF() throws TokenStreamException, CharStreamException {
      try {
         selector.pop(); // return to old lexer/stream
         Debug.out("Popped lexer.");
         selector.retry();
      } catch (NoSuchElementException e) {
         // return a real EOF if nothing in stack
      }
    }

   private String modalityBegin = null;
   private String modalityEnd = null;

   private static HashMap<String,String> modNames = new HashMap<String,String>(20);
   private static HashMap<String,String> modPairs = new HashMap<String,String>(20);
   
   static {
      modNames.put("\\<","diamond");
      modNames.put("\\diamond","diamond");
      modNames.put("\\diamond_transaction","diamond_transaction");
      modNames.put("\\[","box");
      modNames.put("\\box","box");
      modNames.put("\\box_transaction","box_transaction");
      modNames.put("\\[[","throughout");
      modNames.put("\\throughout","throughout");
      modNames.put("\\throughout_transaction","throughout_transaction");

      modPairs.put("\\<","\\>");
      modPairs.put("\\modality","\\endmodality");
      modPairs.put("\\diamond","\\endmodality");
      modPairs.put("\\diamond_transaction","\\endmodality");
      modPairs.put("\\[","\\]");
      modPairs.put("\\box","\\endmodality");
      modPairs.put("\\box_transaction","\\endmodality");
      modPairs.put("\\[[","\\]]");
      modPairs.put("\\throughout","\\endmodality");
      modPairs.put("\\throughout_transaction","\\endmodality");
   }
   
   public void recover( RecognitionException ex, BitSet tokenSet ) throws CharStreamException {
     consume();
     consumeUntil( tokenSet );
   }

   private void matchAndTransformModality(int beginIndex) throws antlr.RecognitionException {
      if(!modalityEnd.equals((String)modPairs.get(modalityBegin)))
          throw new RecognitionException("Unknown modality " +
	   "expression "+modalityBegin+"..."+modalityEnd+".",
	     getFilename(), getLine(), getColumn());

      antlr.ANTLRStringBuffer newText = new antlr.ANTLRStringBuffer();
      int index = 0;
      int first = 0;
      int last = 0;
      String s = text.toString();
      newText.append(s.substring(0,beginIndex));
      index = beginIndex + modalityBegin.length();
      String modName = "";
      if("\\modality".equals(modalityBegin)) {
         // Have to extract the name of (schema) modality inside the first {}
	 while(s.charAt(index) == ' ' || s.charAt(index) == '\t' ||
      	       s.charAt(index) == '\n' || s.charAt(index) == '\r') index++;
	 if(s.charAt(index) != '{') {
           throw new RecognitionException("Expression "+modalityBegin+" should be followed by {...}.",
	     getFilename(), getLine(), getColumn());
	 }
         index++;
	 first = index;
	 char currChar = s.charAt(index);
	 while(currChar == ' ' || currChar == '\t' ||
	       currChar == '\r' || currChar == '\n') {
	     index++; first = index;
	     currChar = s.charAt(index);
	 }
	 last = first;
	 while((currChar >= 'a' && currChar <= 'z') ||
	        (currChar >= 'A' && currChar <= 'Z') ||
		currChar == '_' || currChar == '#') {
	     index++; last = index;
	     currChar = s.charAt(index);
	 }
	 while(currChar == ' ' || currChar == '\t' ||
	       currChar == '\r' || currChar == '\n') {
	     index++;
	     currChar = s.charAt(index);
	 }
	 if(s.charAt(index) != '}') {
            throw new RecognitionException("Expected '}', found "+s.charAt(index)+".", getFilename(), getLine(), getColumn());
         }
	 index++;
	 modName=s.substring(first,last);
	 if("".equals(modName)) {
            throw new RecognitionException("Empty modality name. Modality block	was: "+s, getFilename(), getLine(), getColumn());
	 }
      }else{
         modName = (String)modNames.get(modalityBegin);
	 if(modName==null) {
            throw new RecognitionException("Unknown modality "+modalityBegin+".", getFilename(), getLine(), getColumn());
	 }

      }
      newText.append(modName+"\n");
      Debug.out("Modality name :", modName);
      last = s.lastIndexOf(modalityEnd);
      newText.append(s.substring(index,last));
      text = newText;
      Debug.out("Lexer: recognised Java block string: ", text);
   }

public KeYLexer(InputStream in) {
	this(new ByteBuffer(in));
}
public KeYLexer(Reader in) {
	this(new CharBuffer(in));
}
public KeYLexer(InputBuffer ib) {
	this(new LexerSharedInputState(ib));
}
public KeYLexer(LexerSharedInputState state) {
	super(state);
	caseSensitiveLiterals = true;
	setCaseSensitive(true);
	literals = new Hashtable();
	literals.put(new ANTLRHashString("\\replacewith", this), new Integer(82));
	literals.put(new ANTLRHashString("\\antecedentPolarity", this), new Integer(75));
	literals.put(new ANTLRHashString("\\isObserver", this), new Integer(38));
	literals.put(new ANTLRHashString("\\else", this), new Integer(61));
	literals.put(new ANTLRHashString("\\helptext", this), new Integer(81));
	literals.put(new ANTLRHashString("\\formula", this), new Integer(13));
	literals.put(new ANTLRHashString("\\strict", this), new Integer(52));
	literals.put(new ANTLRHashString("\\functions", this), new Integer(90));
	literals.put(new ANTLRHashString("\\typeof", this), new Integer(53));
	literals.put(new ANTLRHashString("\\bigint", this), new Integer(105));
	literals.put(new ANTLRHashString("\\isReference", this), new Integer(41));
	literals.put(new ANTLRHashString("\\succedentPolarity", this), new Integer(76));
	literals.put(new ANTLRHashString("\\elemSort", this), new Integer(32));
	literals.put(new ANTLRHashString("\\addrules", this), new Integer(83));
	literals.put(new ANTLRHashString("\\classpath", this), new Integer(64));
	literals.put(new ANTLRHashString("\\include", this), new Integer(62));
	literals.put(new ANTLRHashString("\\dropEffectlessElementaries", this), new Integer(25));
	literals.put(new ANTLRHashString("\\abstract", this), new Integer(8));
	literals.put(new ANTLRHashString("\\term", this), new Integer(14));
	literals.put(new ANTLRHashString("\\heuristics", this), new Integer(85));
	literals.put(new ANTLRHashString("\\sameUpdateLevel", this), new Integer(73));
	literals.put(new ANTLRHashString("\\disjointModuloNull", this), new Integer(24));
	literals.put(new ANTLRHashString("\\programVariables", this), new Integer(20));
	literals.put(new ANTLRHashString("\\variables", this), new Integer(16));
	literals.put(new ANTLRHashString("\\inType", this), new Integer(99));
	literals.put(new ANTLRHashString("\\heuristicsDecl", this), new Integer(78));
	literals.put(new ANTLRHashString("\\predicates", this), new Integer(89));
	literals.put(new ANTLRHashString("\\settings", this), new Integer(70));
	literals.put(new ANTLRHashString("\\bootclasspath", this), new Integer(65));
	literals.put(new ANTLRHashString("\\fieldType", this), new Integer(31));
	literals.put(new ANTLRHashString("\\seq", this), new Integer(104));
	literals.put(new ANTLRHashString("\\addprogvars", this), new Integer(84));
	literals.put(new ANTLRHashString("\\sorts", this), new Integer(4));
	literals.put(new ANTLRHashString("\\locset", this), new Integer(103));
	literals.put(new ANTLRHashString("\\noninteractive", this), new Integer(79));
	literals.put(new ANTLRHashString("\\simplifyIfThenElseUpdate", this), new Integer(27));
	literals.put(new ANTLRHashString("\\isAbstractOrInterface", this), new Integer(100));
	literals.put(new ANTLRHashString("\\modalOperator", this), new Integer(11));
	literals.put(new ANTLRHashString("\\oneof", this), new Integer(7));
	literals.put(new ANTLRHashString("\\isArrayLength", this), new Integer(34));
	literals.put(new ANTLRHashString("\\metaDisjoint", this), new Integer(40));
	literals.put(new ANTLRHashString("\\then", this), new Integer(60));
	literals.put(new ANTLRHashString("\\includeLDTs", this), new Integer(63));
	literals.put(new ANTLRHashString("\\inSequentState", this), new Integer(74));
	literals.put(new ANTLRHashString("\\sub", this), new Integer(43));
	literals.put(new ANTLRHashString("\\schemaVar", this), new Integer(10));
	literals.put(new ANTLRHashString("\\varcond", this), new Integer(21));
	literals.put(new ANTLRHashString("\\skolemTerm", this), new Integer(17));
	literals.put(new ANTLRHashString("\\invariants", this), new Integer(98));
	literals.put(new ANTLRHashString("\\javaSource", this), new Integer(67));
	literals.put(new ANTLRHashString("\\extends", this), new Integer(6));
	literals.put(new ANTLRHashString("\\forall", this), new Integer(55));
	literals.put(new ANTLRHashString("\\displayname", this), new Integer(80));
	literals.put(new ANTLRHashString("\\contracts", this), new Integer(97));
	literals.put(new ANTLRHashString("\\generic", this), new Integer(5));
	literals.put(new ANTLRHashString("\\containerType", this), new Integer(101));
	literals.put(new ANTLRHashString("\\ifEx", this), new Integer(59));
	literals.put(new ANTLRHashString("$lmtd", this), new Integer(102));
	literals.put(new ANTLRHashString("\\schemaVariables", this), new Integer(9));
	literals.put(new ANTLRHashString("\\optionsDecl", this), new Integer(69));
	literals.put(new ANTLRHashString("\\newLabel", this), new Integer(46));
	literals.put(new ANTLRHashString("\\static", this), new Integer(50));
	literals.put(new ANTLRHashString("\\enumConstant", this), new Integer(28));
	literals.put(new ANTLRHashString("\\exists", this), new Integer(56));
	literals.put(new ANTLRHashString("\\instantiateGeneric", this), new Integer(54));
	literals.put(new ANTLRHashString("\\subst", this), new Integer(57));
	literals.put(new ANTLRHashString("\\dependingOn", this), new Integer(23));
	literals.put(new ANTLRHashString("\\chooseContract", this), new Integer(94));
	literals.put(new ANTLRHashString("\\isLocalVariable", this), new Integer(37));
	literals.put(new ANTLRHashString("\\proof", this), new Integer(96));
	literals.put(new ANTLRHashString("\\hasSort", this), new Integer(30));
	literals.put(new ANTLRHashString("\\modifies", this), new Integer(19));
	literals.put(new ANTLRHashString("\\closegoal", this), new Integer(77));
	literals.put(new ANTLRHashString("\\rules", this), new Integer(92));
	literals.put(new ANTLRHashString("\\applyUpdateOnRigid", this), new Integer(22));
	literals.put(new ANTLRHashString("\\new", this), new Integer(45));
	literals.put(new ANTLRHashString("\\update", this), new Integer(15));
	literals.put(new ANTLRHashString("\\find", this), new Integer(86));
	literals.put(new ANTLRHashString("\\same", this), new Integer(49));
	literals.put(new ANTLRHashString("\\skolemFormula", this), new Integer(18));
	literals.put(new ANTLRHashString("false", this), new Integer(72));
	literals.put(new ANTLRHashString("\\assumes", this), new Integer(88));
	literals.put(new ANTLRHashString("\\isArray", this), new Integer(33));
	literals.put(new ANTLRHashString("\\proofObligation", this), new Integer(95));
	literals.put(new ANTLRHashString("\\different", this), new Integer(39));
	literals.put(new ANTLRHashString("\\program", this), new Integer(12));
	literals.put(new ANTLRHashString("\\unique", this), new Integer(91));
	literals.put(new ANTLRHashString("\\isInductVar", this), new Integer(36));
	literals.put(new ANTLRHashString("\\staticMethodReference", this), new Integer(51));
	literals.put(new ANTLRHashString("\\not", this), new Integer(47));
	literals.put(new ANTLRHashString("\\isReferenceArray", this), new Integer(42));
	literals.put(new ANTLRHashString("\\problem", this), new Integer(93));
	literals.put(new ANTLRHashString("\\noDefaultClasses", this), new Integer(66));
	literals.put(new ANTLRHashString("\\freeLabelIn", this), new Integer(29));
	literals.put(new ANTLRHashString("\\add", this), new Integer(87));
	literals.put(new ANTLRHashString("\\isEnumType", this), new Integer(35));
	literals.put(new ANTLRHashString("\\withOptions", this), new Integer(68));
	literals.put(new ANTLRHashString("true", this), new Integer(71));
	literals.put(new ANTLRHashString("\\notFreeIn", this), new Integer(48));
	literals.put(new ANTLRHashString("\\equalUnique", this), new Integer(44));
	literals.put(new ANTLRHashString("\\dropEffectlessStores", this), new Integer(26));
	literals.put(new ANTLRHashString("\\if", this), new Integer(58));
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
				switch ( LA(1)) {
				case ';':
				{
					mSEMI(true);
					theRetToken=_returnToken;
					break;
				}
				case ',':
				{
					mCOMMA(true);
					theRetToken=_returnToken;
					break;
				}
				case '(':
				{
					mLPAREN(true);
					theRetToken=_returnToken;
					break;
				}
				case ')':
				{
					mRPAREN(true);
					theRetToken=_returnToken;
					break;
				}
				case '{':
				{
					mLBRACE(true);
					theRetToken=_returnToken;
					break;
				}
				case '}':
				{
					mRBRACE(true);
					theRetToken=_returnToken;
					break;
				}
				case ']':
				{
					mRBRACKET(true);
					theRetToken=_returnToken;
					break;
				}
				case '@':
				{
					mAT(true);
					theRetToken=_returnToken;
					break;
				}
				case '&':
				{
					mAND(true);
					theRetToken=_returnToken;
					break;
				}
				case '^':
				{
					mEXP(true);
					theRetToken=_returnToken;
					break;
				}
				case '~':
				{
					mTILDE(true);
					theRetToken=_returnToken;
					break;
				}
				case '%':
				{
					mPERCENT(true);
					theRetToken=_returnToken;
					break;
				}
				case '*':
				{
					mSTAR(true);
					theRetToken=_returnToken;
					break;
				}
				case '+':
				{
					mPLUS(true);
					theRetToken=_returnToken;
					break;
				}
				case '\t':  case '\n':  case '\r':  case ' ':
				{
					mWS(true);
					theRetToken=_returnToken;
					break;
				}
				case '"':
				{
					mSTRING_LITERAL(true);
					theRetToken=_returnToken;
					break;
				}
				case '<':
				{
					mLESS_DISPATCH(true);
					theRetToken=_returnToken;
					break;
				}
				case '\'':
				{
					mPRIMES_OR_CHARLITERAL(true);
					theRetToken=_returnToken;
					break;
				}
				case '0':  case '1':  case '2':  case '3':
				case '4':  case '5':  case '6':  case '7':
				case '8':  case '9':
				{
					mDIGIT_DISPATCH(true);
					theRetToken=_returnToken;
					break;
				}
				case '#':  case '$':  case 'A':  case 'B':
				case 'C':  case 'D':  case 'E':  case 'F':
				case 'G':  case 'H':  case 'I':  case 'J':
				case 'K':  case 'L':  case 'M':  case 'N':
				case 'O':  case 'P':  case 'Q':  case 'R':
				case 'S':  case 'T':  case 'U':  case 'V':
				case 'W':  case 'X':  case 'Y':  case 'Z':
				case '_':  case 'a':  case 'b':  case 'c':
				case 'd':  case 'e':  case 'f':  case 'g':
				case 'h':  case 'i':  case 'j':  case 'k':
				case 'l':  case 'm':  case 'n':  case 'o':
				case 'p':  case 'q':  case 'r':  case 's':
				case 't':  case 'u':  case 'v':  case 'w':
				case 'x':  case 'y':  case 'z':
				{
					mIDENT(true);
					theRetToken=_returnToken;
					break;
				}
				case '\\':
				{
					mMODALITY(true);
					theRetToken=_returnToken;
					break;
				}
				default:
					if ((LA(1)==':') && (LA(2)==':')) {
						mDOUBLECOLON(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)==':') && (LA(2)=='=')) {
						mASSIGN(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='.') && (LA(2)=='.')) {
						mDOTRANGE(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='[') && (LA(2)==']')) {
						mEMPTYBRACKETS(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='|') && (LA(2)=='|')) {
						mPARALLEL(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='-') && (LA(2)=='>')) {
						mIMP(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='!') && (LA(2)=='=')) {
						mNOT_EQUALS(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='=') && (LA(2)=='=')) {
						mSEQARROW(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='>') && (LA(2)=='=')) {
						mGREATEREQUAL(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='>') && (LA(2)=='>')) {
						mRGUILLEMETS(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='/') && (LA(2)=='/')) {
						mSL_COMMENT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='/') && (LA(2)=='*')) {
						mML_COMMENT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='/') && (true)) {
						mSLASH(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)==':') && (true)) {
						mCOLON(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='.') && (true)) {
						mDOT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='[') && (true)) {
						mLBRACKET(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='|') && (true)) {
						mOR(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='!') && (true)) {
						mNOT(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='=') && (true)) {
						mEQUALS(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='-') && (true)) {
						mMINUS(true);
						theRetToken=_returnToken;
					}
					else if ((LA(1)=='>') && (true)) {
						mGREATER(true);
						theRetToken=_returnToken;
					}
				else {
					if (LA(1)==EOF_CHAR) {uponEOF(); _returnToken = makeToken(Token.EOF_TYPE);}
				else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				}
				if ( _returnToken==null ) continue tryAgain; // found SKIP token
				_ttype = _returnToken.getType();
				_ttype = testLiteralsTable(_ttype);
				_returnToken.setType(_ttype);
				return _returnToken;
			}
			catch (RecognitionException e) {
				reportError(e);
				consume();
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

	protected final void mVOCAB(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = VOCAB;
		int _saveIndex;
		
		try {      // for error handling
			matchRange('\3','\377');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSEMI(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SEMI;
		int _saveIndex;
		
		try {      // for error handling
			match(';');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSLASH(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SLASH;
		int _saveIndex;
		
		try {      // for error handling
			match('/');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mCOLON(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = COLON;
		int _saveIndex;
		
		try {      // for error handling
			match(':');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDOUBLECOLON(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOUBLECOLON;
		int _saveIndex;
		
		try {      // for error handling
			match("::");
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mASSIGN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ASSIGN;
		int _saveIndex;
		
		try {      // for error handling
			match(":=");
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDOT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOT;
		int _saveIndex;
		
		try {      // for error handling
			match('.');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDOTRANGE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DOTRANGE;
		int _saveIndex;
		
		try {      // for error handling
			match('.');
			match('.');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mCOMMA(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = COMMA;
		int _saveIndex;
		
		try {      // for error handling
			match(',');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLPAREN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LPAREN;
		int _saveIndex;
		
		try {      // for error handling
			match('(');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mRPAREN(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = RPAREN;
		int _saveIndex;
		
		try {      // for error handling
			match(')');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLBRACE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LBRACE;
		int _saveIndex;
		
		try {      // for error handling
			match('{');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mRBRACE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = RBRACE;
		int _saveIndex;
		
		try {      // for error handling
			match('}');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLBRACKET(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LBRACKET;
		int _saveIndex;
		
		try {      // for error handling
			match('[');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mRBRACKET(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = RBRACKET;
		int _saveIndex;
		
		try {      // for error handling
			match(']');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mEMPTYBRACKETS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = EMPTYBRACKETS;
		int _saveIndex;
		
		try {      // for error handling
			match('[');
			match(']');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mAT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = AT;
		int _saveIndex;
		
		try {      // for error handling
			match('@');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mPARALLEL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PARALLEL;
		int _saveIndex;
		
		try {      // for error handling
			match('|');
			match('|');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mOR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = OR;
		int _saveIndex;
		
		try {      // for error handling
			match('|');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mAND(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = AND;
		int _saveIndex;
		
		try {      // for error handling
			match('&');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mNOT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NOT;
		int _saveIndex;
		
		try {      // for error handling
			match('!');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mIMP(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = IMP;
		int _saveIndex;
		
		try {      // for error handling
			match("->");
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mEQUALS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = EQUALS;
		int _saveIndex;
		
		try {      // for error handling
			match("=");
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mNOT_EQUALS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NOT_EQUALS;
		int _saveIndex;
		
		try {      // for error handling
			match("!=");
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSEQARROW(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SEQARROW;
		int _saveIndex;
		
		try {      // for error handling
			match("==>");
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mEXP(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = EXP;
		int _saveIndex;
		
		try {      // for error handling
			match('^');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mTILDE(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = TILDE;
		int _saveIndex;
		
		try {      // for error handling
			match('~');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mPERCENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PERCENT;
		int _saveIndex;
		
		try {      // for error handling
			match('%');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSTAR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = STAR;
		int _saveIndex;
		
		try {      // for error handling
			match('*');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mMINUS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = MINUS;
		int _saveIndex;
		
		try {      // for error handling
			match('-');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mPLUS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PLUS;
		int _saveIndex;
		
		try {      // for error handling
			match('+');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mGREATER(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = GREATER;
		int _saveIndex;
		
		try {      // for error handling
			match('>');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mGREATEREQUAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = GREATEREQUAL;
		int _saveIndex;
		
		try {      // for error handling
			match('>');
			match('=');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mRGUILLEMETS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = RGUILLEMETS;
		int _saveIndex;
		
		try {      // for error handling
			match('>');
			match('>');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
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
		
		try {      // for error handling
			{
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
					newline();
				}
				break;
			}
			case '\r':
			{
				match('\r');
				if ( inputState.guessing==0 ) {
					if(LA(1) != '\n') newline();
				}
				break;
			}
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				_ttype = Token.SKIP;
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
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
		
		try {      // for error handling
			match('"');
			{
			_loop40:
			do {
				switch ( LA(1)) {
				case '\\':
				{
					mESC(false);
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
					if ((_tokenSet_1.member(LA(1)))) {
						{
						match(_tokenSet_1);
						}
					}
				else {
					break _loop40;
				}
				}
			} while (true);
			}
			match('"');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
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
		
		try {      // for error handling
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
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mLESS_DISPATCH(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LESS_DISPATCH;
		int _saveIndex;
		
		try {      // for error handling
			boolean synPredMatched45 = false;
			if (((LA(1)=='<') && (_tokenSet_3.member(LA(2))))) {
				int _m45 = mark();
				synPredMatched45 = true;
				inputState.guessing++;
				try {
					{
					match('<');
					{
					int _cnt44=0;
					_loop44:
					do {
						if ((_tokenSet_3.member(LA(1)))) {
							mLETTER(false);
						}
						else {
							if ( _cnt44>=1 ) { break _loop44; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
						}
						
						_cnt44++;
					} while (true);
					}
					match('>');
					}
				}
				catch (RecognitionException pe) {
					synPredMatched45 = false;
				}
				rewind(_m45);
inputState.guessing--;
			}
			if ( synPredMatched45 ) {
				mIMPLICIT_IDENT(false);
				if ( inputState.guessing==0 ) {
					_ttype = IDENT;
				}
			}
			else {
				boolean synPredMatched47 = false;
				if (((LA(1)=='<') && (LA(2)=='-'))) {
					int _m47 = mark();
					synPredMatched47 = true;
					inputState.guessing++;
					try {
						{
						match('<');
						match('-');
						match('>');
						}
					}
					catch (RecognitionException pe) {
						synPredMatched47 = false;
					}
					rewind(_m47);
inputState.guessing--;
				}
				if ( synPredMatched47 ) {
					mEQV(false);
					if ( inputState.guessing==0 ) {
						_ttype = EQV;
					}
				}
				else {
					boolean synPredMatched49 = false;
					if (((LA(1)=='<') && (LA(2)=='='))) {
						int _m49 = mark();
						synPredMatched49 = true;
						inputState.guessing++;
						try {
							{
							match('<');
							match('=');
							}
						}
						catch (RecognitionException pe) {
							synPredMatched49 = false;
						}
						rewind(_m49);
inputState.guessing--;
					}
					if ( synPredMatched49 ) {
						mLESSEQUAL(false);
						if ( inputState.guessing==0 ) {
							_ttype = LESSEQUAL;
						}
					}
					else {
						boolean synPredMatched51 = false;
						if (((LA(1)=='<') && (LA(2)=='<'))) {
							int _m51 = mark();
							synPredMatched51 = true;
							inputState.guessing++;
							try {
								{
								match('<');
								match('<');
								}
							}
							catch (RecognitionException pe) {
								synPredMatched51 = false;
							}
							rewind(_m51);
inputState.guessing--;
						}
						if ( synPredMatched51 ) {
							mLGUILLEMETS(false);
							if ( inputState.guessing==0 ) {
								_ttype = LGUILLEMETS;
							}
						}
						else if ((LA(1)=='<') && (true)) {
							mLESS(false);
							if ( inputState.guessing==0 ) {
								_ttype = LESS;
							}
						}
						else {
							throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
						}
						}}}
					}
					catch (RecognitionException ex) {
						if (inputState.guessing==0) {
							reportError(ex);
							recover(ex,_tokenSet_0);
						} else {
						  throw ex;
						}
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
		
		try {      // for error handling
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
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mIMPLICIT_IDENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = IMPLICIT_IDENT;
		int _saveIndex;
		
		try {      // for error handling
			match('<');
			{
			int _cnt57=0;
			_loop57:
			do {
				if ((_tokenSet_3.member(LA(1)))) {
					mLETTER(false);
				}
				else {
					if ( _cnt57>=1 ) { break _loop57; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				
				_cnt57++;
			} while (true);
			}
			match('>');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mEQV(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = EQV;
		int _saveIndex;
		
		try {      // for error handling
			match("<->");
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mLESSEQUAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LESSEQUAL;
		int _saveIndex;
		
		try {      // for error handling
			match('<');
			match('=');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mLGUILLEMETS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LGUILLEMETS;
		int _saveIndex;
		
		try {      // for error handling
			match('<');
			match('<');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mLESS(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = LESS;
		int _saveIndex;
		
		try {      // for error handling
			match('<');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mPRIMES_OR_CHARLITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PRIMES_OR_CHARLITERAL;
		int _saveIndex;
		
		try {      // for error handling
			boolean synPredMatched63 = false;
			if (((LA(1)=='\'') && (_tokenSet_5.member(LA(2))))) {
				int _m63 = mark();
				synPredMatched63 = true;
				inputState.guessing++;
				try {
					{
					match('\'');
					match('\\');
					}
				}
				catch (RecognitionException pe) {
					synPredMatched63 = false;
				}
				rewind(_m63);
inputState.guessing--;
			}
			if ( synPredMatched63 ) {
				mCHAR_LITERAL(false);
				if ( inputState.guessing==0 ) {
					_ttype = CHAR_LITERAL;
				}
			}
			else {
				boolean synPredMatched66 = false;
				if (((LA(1)=='\'') && (_tokenSet_5.member(LA(2))))) {
					int _m66 = mark();
					synPredMatched66 = true;
					inputState.guessing++;
					try {
						{
						match('\'');
						{
						match(_tokenSet_6);
						}
						match('\'');
						}
					}
					catch (RecognitionException pe) {
						synPredMatched66 = false;
					}
					rewind(_m66);
inputState.guessing--;
				}
				if ( synPredMatched66 ) {
					mCHAR_LITERAL(false);
					if ( inputState.guessing==0 ) {
						_ttype = CHAR_LITERAL;
					}
				}
				else {
					boolean synPredMatched61 = false;
					if (((LA(1)=='\'') && (true))) {
						int _m61 = mark();
						synPredMatched61 = true;
						inputState.guessing++;
						try {
							{
							match('\'');
							match('\'');
							}
						}
						catch (RecognitionException pe) {
							synPredMatched61 = false;
						}
						rewind(_m61);
inputState.guessing--;
					}
					if ( synPredMatched61 ) {
						mPRIMES(false);
						if ( inputState.guessing==0 ) {
							_ttype = PRIMES;
						}
					}
					else if ((LA(1)=='\'') && (true)) {
						mPRIMES(false);
						if ( inputState.guessing==0 ) {
							_ttype = PRIMES;
						}
					}
					else {
						throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
					}
					}}
				}
				catch (RecognitionException ex) {
					if (inputState.guessing==0) {
						reportError(ex);
						recover(ex,_tokenSet_0);
					} else {
					  throw ex;
					}
				}
				if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
					_token = makeToken(_ttype);
					_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
				}
				_returnToken = _token;
			}
			
	protected final void mPRIMES(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = PRIMES;
		int _saveIndex;
		
		try {      // for error handling
			{
			int _cnt69=0;
			_loop69:
			do {
				if ((LA(1)=='\'')) {
					match('\'');
				}
				else {
					if ( _cnt69>=1 ) { break _loop69; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				
				_cnt69++;
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mCHAR_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = CHAR_LITERAL;
		int _saveIndex;
		
		try {      // for error handling
			match('\'');
			{
			switch ( LA(1)) {
			case ' ':  case '!':  case '"':  case '#':
			case '$':  case '%':  case '&':
			{
				{
				matchRange(' ','&');
				}
				break;
			}
			case '(':  case ')':  case '*':  case '+':
			case ',':  case '-':  case '.':  case '/':
			case '0':  case '1':  case '2':  case '3':
			case '4':  case '5':  case '6':  case '7':
			case '8':  case '9':  case ':':  case ';':
			case '<':  case '=':  case '>':  case '?':
			case '@':  case 'A':  case 'B':  case 'C':
			case 'D':  case 'E':  case 'F':  case 'G':
			case 'H':  case 'I':  case 'J':  case 'K':
			case 'L':  case 'M':  case 'N':  case 'O':
			case 'P':  case 'Q':  case 'R':  case 'S':
			case 'T':  case 'U':  case 'V':  case 'W':
			case 'X':  case 'Y':  case 'Z':  case '[':
			{
				{
				matchRange('(','[');
				}
				break;
			}
			case ']':  case '^':  case '_':  case '`':
			case 'a':  case 'b':  case 'c':  case 'd':
			case 'e':  case 'f':  case 'g':  case 'h':
			case 'i':  case 'j':  case 'k':  case 'l':
			case 'm':  case 'n':  case 'o':  case 'p':
			case 'q':  case 'r':  case 's':  case 't':
			case 'u':  case 'v':  case 'w':  case 'x':
			case 'y':  case 'z':  case '{':  case '|':
			case '}':  case '~':
			{
				{
				matchRange(']','~');
				}
				break;
			}
			case '\\':
			{
				{
				match('\\');
				{
				switch ( LA(1)) {
				case '\'':
				{
					match('\'');
					break;
				}
				case '\\':
				{
					match('\\');
					break;
				}
				case 'n':
				{
					match('n');
					break;
				}
				case 'r':
				{
					match('r');
					break;
				}
				case 't':
				{
					match('t');
					break;
				}
				case 'b':
				{
					match('b');
					break;
				}
				case 'f':
				{
					match('f');
					break;
				}
				case '"':
				{
					match('"');
					break;
				}
				case 'u':
				{
					match('u');
					mHEX(false);
					break;
				}
				default:
				{
					throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
				}
				}
				}
				}
				break;
			}
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			match('\'');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_7);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mHEX(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = HEX;
		int _saveIndex;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case 'a':  case 'b':  case 'c':  case 'd':
			case 'e':  case 'f':
			{
				matchRange('a','f');
				break;
			}
			case 'A':  case 'B':  case 'C':  case 'D':
			case 'E':  case 'F':
			{
				matchRange('A','F');
				break;
			}
			case '0':  case '1':  case '2':  case '3':
			case '4':  case '5':  case '6':  case '7':
			case '8':  case '9':
			{
				mDIGIT(false);
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
			case 'a':  case 'b':  case 'c':  case 'd':
			case 'e':  case 'f':
			{
				matchRange('a','f');
				break;
			}
			case 'A':  case 'B':  case 'C':  case 'D':
			case 'E':  case 'F':
			{
				matchRange('A','F');
				break;
			}
			case '0':  case '1':  case '2':  case '3':
			case '4':  case '5':  case '6':  case '7':
			case '8':  case '9':
			{
				mDIGIT(false);
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
			case 'a':  case 'b':  case 'c':  case 'd':
			case 'e':  case 'f':
			{
				matchRange('a','f');
				break;
			}
			case 'A':  case 'B':  case 'C':  case 'D':
			case 'E':  case 'F':
			{
				matchRange('A','F');
				break;
			}
			case '0':  case '1':  case '2':  case '3':
			case '4':  case '5':  case '6':  case '7':
			case '8':  case '9':
			{
				mDIGIT(false);
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
			case 'a':  case 'b':  case 'c':  case 'd':
			case 'e':  case 'f':
			{
				matchRange('a','f');
				break;
			}
			case 'A':  case 'B':  case 'C':  case 'D':
			case 'E':  case 'F':
			{
				matchRange('A','F');
				break;
			}
			case '0':  case '1':  case '2':  case '3':
			case '4':  case '5':  case '6':  case '7':
			case '8':  case '9':
			{
				mDIGIT(false);
				break;
			}
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_8);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mQUOTED_STRING_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = QUOTED_STRING_LITERAL;
		int _saveIndex;
		
		try {      // for error handling
			match('"');
			{
			_loop82:
			do {
				switch ( LA(1)) {
				case '\\':
				{
					match('\\');
					matchNot(EOF_CHAR);
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
					if ((_tokenSet_9.member(LA(1)))) {
						{
						match(_tokenSet_9);
						}
					}
				else {
					break _loop82;
				}
				}
			} while (true);
			}
			match('"');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_7);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mSL_COMMENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = SL_COMMENT;
		int _saveIndex;
		
		try {      // for error handling
			match("//");
			{
			_loop86:
			do {
				if ((_tokenSet_10.member(LA(1)))) {
					{
					match(_tokenSet_10);
					}
				}
				else {
					break _loop86;
				}
				
			} while (true);
			}
			{
			switch ( LA(1)) {
			case '\n':
			{
				match('\n');
				break;
			}
			case '\uffff':
			{
				match('\uFFFF');
				break;
			}
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				_ttype = Token.SKIP; newline();
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_7);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mML_COMMENT(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = ML_COMMENT;
		int _saveIndex;
		
		try {      // for error handling
			match("/*");
			if ( inputState.guessing==0 ) {
				
					  while(true) {
					    if((LA(1) == '\r' && LA(2) != '\n') ||
						LA(1) == '\n') newline();
					    if(LA(1) == '*' && LA(2) == '/') {
					      match("*/");
					      break;
					    }
					    matchNot(EOF_CHAR);
					  }
					  _ttype = Token.SKIP;
					
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_7);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	public final void mDIGIT_DISPATCH(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = DIGIT_DISPATCH;
		int _saveIndex;
		
		try {      // for error handling
			boolean synPredMatched95 = false;
			if (((LA(1)=='0') && (LA(2)=='x'))) {
				int _m95 = mark();
				synPredMatched95 = true;
				inputState.guessing++;
				try {
					{
					match('0');
					match('x');
					}
				}
				catch (RecognitionException pe) {
					synPredMatched95 = false;
				}
				rewind(_m95);
inputState.guessing--;
			}
			if ( synPredMatched95 ) {
				mHEX_LITERAL(false);
				if ( inputState.guessing==0 ) {
					_ttype = NUM_LITERAL;
				}
			}
			else {
				boolean synPredMatched93 = false;
				if ((((LA(1) >= '0' && LA(1) <= '9')) && (true))) {
					int _m93 = mark();
					synPredMatched93 = true;
					inputState.guessing++;
					try {
						{
						mDIGIT(false);
						{
						_loop92:
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
							case '\r':
							{
								match('\r');
								break;
							}
							case '\n':
							{
								match('\n');
								break;
							}
							default:
							{
								break _loop92;
							}
							}
						} while (true);
						}
						mLPAREN(false);
						}
					}
					catch (RecognitionException pe) {
						synPredMatched93 = false;
					}
					rewind(_m93);
inputState.guessing--;
				}
				if ( synPredMatched93 ) {
					mDIGIT(false);
					if ( inputState.guessing==0 ) {
						_ttype = IDENT;
					}
				}
				else if (((LA(1) >= '0' && LA(1) <= '9')) && (true)) {
					mNUM_LITERAL(false);
					if ( inputState.guessing==0 ) {
						_ttype = NUM_LITERAL;
					}
				}
				else {
					throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
				}
				}
			}
			catch (RecognitionException ex) {
				if (inputState.guessing==0) {
					reportError(ex);
					recover(ex,_tokenSet_0);
				} else {
				  throw ex;
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
		
		try {      // for error handling
			matchRange('0','9');
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_11);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mHEX_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = HEX_LITERAL;
		int _saveIndex;
		
		try {      // for error handling
			match('0');
			match('x');
			{
			int _cnt98=0;
			_loop98:
			do {
				switch ( LA(1)) {
				case '0':  case '1':  case '2':  case '3':
				case '4':  case '5':  case '6':  case '7':
				case '8':  case '9':
				{
					mDIGIT(false);
					break;
				}
				case 'a':  case 'b':  case 'c':  case 'd':
				case 'e':  case 'f':
				{
					matchRange('a','f');
					break;
				}
				case 'A':  case 'B':  case 'C':  case 'D':
				case 'E':  case 'F':
				{
					matchRange('A','F');
					break;
				}
				default:
				{
					if ( _cnt98>=1 ) { break _loop98; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				}
				_cnt98++;
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mNUM_LITERAL(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = NUM_LITERAL;
		int _saveIndex;
		
		try {      // for error handling
			{
			int _cnt114=0;
			_loop114:
			do {
				if (((LA(1) >= '0' && LA(1) <= '9'))) {
					mDIGIT(false);
				}
				else {
					if ( _cnt114>=1 ) { break _loop114; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
				}
				
				_cnt114++;
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mIDCHAR(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = IDCHAR;
		int _saveIndex;
		
		try {      // for error handling
			switch ( LA(1)) {
			case 'A':  case 'B':  case 'C':  case 'D':
			case 'E':  case 'F':  case 'G':  case 'H':
			case 'I':  case 'J':  case 'K':  case 'L':
			case 'M':  case 'N':  case 'O':  case 'P':
			case 'Q':  case 'R':  case 'S':  case 'T':
			case 'U':  case 'V':  case 'W':  case 'X':
			case 'Y':  case 'Z':  case 'a':  case 'b':
			case 'c':  case 'd':  case 'e':  case 'f':
			case 'g':  case 'h':  case 'i':  case 'j':
			case 'k':  case 'l':  case 'm':  case 'n':
			case 'o':  case 'p':  case 'q':  case 'r':
			case 's':  case 't':  case 'u':  case 'v':
			case 'w':  case 'x':  case 'y':  case 'z':
			{
				mLETTER(false);
				break;
			}
			case '0':  case '1':  case '2':  case '3':
			case '4':  case '5':  case '6':  case '7':
			case '8':  case '9':
			{
				mDIGIT(false);
				break;
			}
			case '_':
			{
				match('_');
				break;
			}
			case '#':
			{
				match('#');
				break;
			}
			case '$':
			{
				match('$');
				break;
			}
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_12);
			} else {
			  throw ex;
			}
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
		
		try {      // for error handling
			{
			{
			switch ( LA(1)) {
			case 'A':  case 'B':  case 'C':  case 'D':
			case 'E':  case 'F':  case 'G':  case 'H':
			case 'I':  case 'J':  case 'K':  case 'L':
			case 'M':  case 'N':  case 'O':  case 'P':
			case 'Q':  case 'R':  case 'S':  case 'T':
			case 'U':  case 'V':  case 'W':  case 'X':
			case 'Y':  case 'Z':  case 'a':  case 'b':
			case 'c':  case 'd':  case 'e':  case 'f':
			case 'g':  case 'h':  case 'i':  case 'j':
			case 'k':  case 'l':  case 'm':  case 'n':
			case 'o':  case 'p':  case 'q':  case 'r':
			case 's':  case 't':  case 'u':  case 'v':
			case 'w':  case 'x':  case 'y':  case 'z':
			{
				mLETTER(false);
				break;
			}
			case '_':
			{
				match('_');
				break;
			}
			case '#':
			{
				match('#');
				break;
			}
			case '$':
			{
				match('$');
				break;
			}
			default:
			{
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			{
			_loop111:
			do {
				if ((_tokenSet_12.member(LA(1)))) {
					mIDCHAR(false);
				}
				else {
					break _loop111;
				}
				
			} while (true);
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		_ttype = testLiteralsTable(_ttype);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
/**
  * Here we have to accept all strings of kind \\[a-z_]
  * and make the decision our selves as to what to do with it
  * (i.e. is it a modality, keyword, or possibly something else)
  */
	public final void mMODALITY(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = MODALITY;
		int _saveIndex;
		
		try {      // for error handling
			match('\\');
			{
			switch ( LA(1)) {
			case 'A':  case 'B':  case 'C':  case 'D':
			case 'E':  case 'F':  case 'G':  case 'H':
			case 'I':  case 'J':  case 'K':  case 'L':
			case 'M':  case 'N':  case 'O':  case 'P':
			case 'Q':  case 'R':  case 'S':  case 'T':
			case 'U':  case 'V':  case 'W':  case 'X':
			case 'Y':  case 'Z':  case '_':  case 'a':
			case 'b':  case 'c':  case 'd':  case 'e':
			case 'f':  case 'g':  case 'h':  case 'i':
			case 'j':  case 'k':  case 'l':  case 'm':
			case 'n':  case 'o':  case 'p':  case 'q':
			case 'r':  case 's':  case 't':  case 'u':
			case 'v':  case 'w':  case 'x':  case 'y':
			case 'z':
			{
				{
				int _cnt118=0;
				_loop118:
				do {
					switch ( LA(1)) {
					case 'A':  case 'B':  case 'C':  case 'D':
					case 'E':  case 'F':  case 'G':  case 'H':
					case 'I':  case 'J':  case 'K':  case 'L':
					case 'M':  case 'N':  case 'O':  case 'P':
					case 'Q':  case 'R':  case 'S':  case 'T':
					case 'U':  case 'V':  case 'W':  case 'X':
					case 'Y':  case 'Z':  case 'a':  case 'b':
					case 'c':  case 'd':  case 'e':  case 'f':
					case 'g':  case 'h':  case 'i':  case 'j':
					case 'k':  case 'l':  case 'm':  case 'n':
					case 'o':  case 'p':  case 'q':  case 'r':
					case 's':  case 't':  case 'u':  case 'v':
					case 'w':  case 'x':  case 'y':  case 'z':
					{
						mLETTER(false);
						break;
					}
					case '_':
					{
						match('_');
						break;
					}
					default:
					{
						if ( _cnt118>=1 ) { break _loop118; } else {throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());}
					}
					}
					_cnt118++;
				} while (true);
				}
				break;
			}
			case '<':
			{
				match("<");
				break;
			}
			default:
				if ((LA(1)=='[') && (LA(2)=='[')) {
					match("[[");
				}
				else if ((LA(1)=='[') && (true)) {
					match("[");
				}
			else {
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
				modalityBegin = text.toString();
				Debug.out("modalityBegin == ", modalityBegin);
				int literalTest = testLiteralsTable(MODALITY);
				Debug.out("testLiteralsTable == ", literalTest);
				_ttype = testLiteralsTable(_ttype);
				if(literalTest == MODALITY && modPairs.get(modalityBegin) != null) {
				/* This while with the following call to mMODALITYEND is 
				* and alternative to calling mJAVABLOCK, but it should be faster
				*/
				while(true) {
				if(LA(1) == '/' && LA(2) == '/') {
				mSL_COMMENT(false); continue;
				}
				if(LA(1) == '/' && LA(2) == '*') {
				mML_COMMENT(false); continue;
				}
				if(LA(1) == '/' && LA(2) == '*') {
				mML_COMMENT(false); continue;
				}
				if(LA(1) == '\"') {
				mQUOTED_STRING_LITERAL(false); continue;
				}
				if(LA(1) == '\'') {
				mCHAR_LITERAL(false); continue;
				}
				if((LA(1) == '\r' && LA(2) != '\n') ||
				LA(1) == '\n') newline();
				if(LA(1) == '\\' && (LA(2) == 'e' || LA(2) == '>' || LA(2) == ']'))
				// check whether it follows an ENDMODALITY
				break;
				matchNot(EOF_CHAR);
				}
				mMODALITYEND(false);
				//              mJAVABLOCK(false);
				matchAndTransformModality(_begin);
				}else{
				if("\\includeFile".equals(modalityBegin)) {
				// File inclusion 
				while(LA(1) == ' ' || LA(1) == '\t' || LA(1) == '\n')
				match(LA(1));
				int startIndex = text.length()+1;
				mQUOTED_STRING_LITERAL(false);
				int stopIndex = text.length()-1;
				while(LA(1) == ' ' || LA(1) == '\t' || LA(1) == '\n')
				match(LA(1));
				mSEMI(false);
				_ttype = Token.SKIP;
				String fileName = text.toString().substring(startIndex,stopIndex);
				Debug.out("File to be included: ", fileName);
				File incf = new File(fileName);
				File f = new File(getFilename());
				if((f.isAbsolute() || f.getParentFile() != null) && !incf.isAbsolute()) {
				f = new File(f.getParentFile(), fileName);
				fileName = f.getAbsolutePath();
				}
				Debug.out("File to be included: ", fileName);
				try {
				KeYLexer sublexer =
				new KeYLexer(
				new DataInputStream(new  
				FileInputStream(fileName)),
				keh, selector);
				sublexer.setFilename(fileName);
				selector.push(sublexer);
				Debug.out("Pushed lexer: ", sublexer);
				selector.retry();
				} catch (FileNotFoundException fnf) {
				throw new RecognitionException("File '" + fileName + "' not found.",
				getFilename(), getLine(), getColumn());
				}
				} else {
				_ttype = IDENT; // make it an IDENT starting with '\\'
				// (it will not contain digits!)
				}
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		_ttype = testLiteralsTable(_ttype);
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mMODALITYEND(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = MODALITYEND;
		int _saveIndex;
		
		try {      // for error handling
			match('\\');
			{
			switch ( LA(1)) {
			case 'e':
			{
				match("endmodality");
				break;
			}
			case '>':
			{
				match(">");
				break;
			}
			default:
				if ((LA(1)==']') && (LA(2)==']')) {
					match("]]");
				}
				else if ((LA(1)==']') && (true)) {
					match("]");
				}
			else {
				throw new NoViableAltForCharException((char)LA(1), getFilename(), getLine(), getColumn());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
					   modalityEnd = new String(text.getBuffer(), _begin, text.length() - _begin);
				Debug.out("modalityEnd == ", modalityEnd);
					
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	protected final void mJAVABLOCK(boolean _createToken) throws RecognitionException, CharStreamException, TokenStreamException {
		int _ttype; Token _token=null; int _begin=text.length();
		_ttype = JAVABLOCK;
		int _saveIndex;
		
		try {      // for error handling
			{
			_loop124:
			do {
				switch ( LA(1)) {
				case '\'':
				{
					mCHAR_LITERAL(false);
					break;
				}
				case '"':
				{
					mQUOTED_STRING_LITERAL(false);
					break;
				}
				case '\r':
				{
					match('\r');
					if ( inputState.guessing==0 ) {
						if(LA(1) != '\n') newline();
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
				case '0':  case '1':  case '2':  case '3':
				case '4':  case '5':  case '6':  case '7':
				case '8':  case '9':
				{
					matchRange('0','9');
					break;
				}
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
				case '{':
				{
					match('{');
					break;
				}
				case '}':
				{
					match('}');
					break;
				}
				case '(':
				{
					match('(');
					break;
				}
				case ')':
				{
					match(')');
					break;
				}
				case '[':
				{
					match('[');
					break;
				}
				case ']':
				{
					match(']');
					break;
				}
				case '<':
				{
					match('<');
					break;
				}
				case '>':
				{
					match('>');
					break;
				}
				case '.':
				{
					match('.');
					break;
				}
				case ',':
				{
					match(',');
					break;
				}
				case ';':
				{
					match(';');
					break;
				}
				case ':':
				{
					match(':');
					break;
				}
				case '?':
				{
					match('?');
					break;
				}
				case '%':
				{
					match('%');
					break;
				}
				case '*':
				{
					match('*');
					break;
				}
				case '-':
				{
					match('-');
					break;
				}
				case '=':
				{
					match('=');
					break;
				}
				case '+':
				{
					match('+');
					break;
				}
				case '~':
				{
					match('~');
					break;
				}
				case '&':
				{
					match('&');
					break;
				}
				case '|':
				{
					match('|');
					break;
				}
				case '^':
				{
					match('^');
					break;
				}
				case '!':
				{
					match('!');
					break;
				}
				case '@':
				{
					match('@');
					break;
				}
				case '#':
				{
					match('#');
					break;
				}
				case '$':
				{
					match('$');
					break;
				}
				default:
					if ((LA(1)=='/') && (LA(2)=='/')) {
						mSL_COMMENT(false);
					}
					else if ((LA(1)=='/') && (LA(2)=='*')) {
						mML_COMMENT(false);
					}
					else if ((LA(1)=='/') && (_tokenSet_13.member(LA(2)))) {
						match('/');
						{
						match(_tokenSet_13);
						}
					}
				else {
					break _loop124;
				}
				}
			} while (true);
			}
			mMODALITYEND(false);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		if ( _createToken && _token==null && _ttype!=Token.SKIP ) {
			_token = makeToken(_ttype);
			_token.setText(new String(text.getBuffer(), _begin, text.length()-_begin));
		}
		_returnToken = _token;
	}
	
	
	private static final long[] mk_tokenSet_0() {
		long[] data = new long[1025];
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = new long[2048];
		data[0]=-17179870209L;
		data[1]=-268435457L;
		for (int i = 2; i<=1022; i++) { data[i]=-1L; }
		data[1023]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = new long[2048];
		for (int i = 0; i<=1022; i++) { data[i]=-1L; }
		data[1023]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	private static final long[] mk_tokenSet_3() {
		long[] data = new long[1025];
		data[1]=576460743847706622L;
		return data;
	}
	public static final BitSet _tokenSet_3 = new BitSet(mk_tokenSet_3());
	private static final long[] mk_tokenSet_4() {
		long[] data = new long[1025];
		data[0]=4899635022681604096L;
		data[1]=576460745995190270L;
		return data;
	}
	public static final BitSet _tokenSet_4 = new BitSet(mk_tokenSet_4());
	private static final long[] mk_tokenSet_5() {
		long[] data = new long[1025];
		data[0]=-554050781184L;
		data[1]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_5 = new BitSet(mk_tokenSet_5());
	private static final long[] mk_tokenSet_6() {
		long[] data = new long[2048];
		data[0]=-549755813889L;
		for (int i = 1; i<=1023; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_6 = new BitSet(mk_tokenSet_6());
	private static final long[] mk_tokenSet_7() {
		long[] data = new long[1025];
		data[0]=-4294957568L;
		data[1]=9223372032559808511L;
		return data;
	}
	public static final BitSet _tokenSet_7 = new BitSet(mk_tokenSet_7());
	private static final long[] mk_tokenSet_8() {
		long[] data = new long[1025];
		data[0]=549755813888L;
		return data;
	}
	public static final BitSet _tokenSet_8 = new BitSet(mk_tokenSet_8());
	private static final long[] mk_tokenSet_9() {
		long[] data = new long[2048];
		data[0]=-17179870209L;
		data[1]=-268435457L;
		for (int i = 2; i<=1023; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_9 = new BitSet(mk_tokenSet_9());
	private static final long[] mk_tokenSet_10() {
		long[] data = new long[2048];
		data[0]=-1025L;
		for (int i = 1; i<=1022; i++) { data[i]=-1L; }
		data[1023]=9223372036854775807L;
		return data;
	}
	public static final BitSet _tokenSet_10 = new BitSet(mk_tokenSet_10());
	private static final long[] mk_tokenSet_11() {
		long[] data = new long[1025];
		data[0]=287949554010030080L;
		data[1]=576460745995190270L;
		return data;
	}
	public static final BitSet _tokenSet_11 = new BitSet(mk_tokenSet_11());
	private static final long[] mk_tokenSet_12() {
		long[] data = new long[1025];
		data[0]=287949004254216192L;
		data[1]=576460745995190270L;
		return data;
	}
	public static final BitSet _tokenSet_12 = new BitSet(mk_tokenSet_12());
	private static final long[] mk_tokenSet_13() {
		long[] data = new long[2048];
		data[0]=-145135534866433L;
		for (int i = 1; i<=1023; i++) { data[i]=-1L; }
		return data;
	}
	public static final BitSet _tokenSet_13 = new BitSet(mk_tokenSet_13());
	
	}
