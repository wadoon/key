// Generated from Solidity.g4 by ANTLR 4.9.3
package de.uka.ilkd.key.parser.solidity;

import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class SolidityParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.9.3", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		T__17=18, T__18=19, T__19=20, T__20=21, T__21=22, T__22=23, T__23=24, 
		T__24=25, T__25=26, T__26=27, T__27=28, T__28=29, T__29=30, T__30=31, 
		T__31=32, T__32=33, T__33=34, T__34=35, T__35=36, T__36=37, T__37=38, 
		T__38=39, T__39=40, T__40=41, T__41=42, T__42=43, T__43=44, T__44=45, 
		T__45=46, T__46=47, T__47=48, T__48=49, T__49=50, T__50=51, T__51=52, 
		T__52=53, T__53=54, T__54=55, T__55=56, T__56=57, T__57=58, T__58=59, 
		T__59=60, T__60=61, T__61=62, T__62=63, T__63=64, T__64=65, T__65=66, 
		T__66=67, T__67=68, T__68=69, T__69=70, T__70=71, T__71=72, T__72=73, 
		T__73=74, T__74=75, T__75=76, T__76=77, T__77=78, T__78=79, T__79=80, 
		T__80=81, T__81=82, T__82=83, T__83=84, T__84=85, T__85=86, T__86=87, 
		T__87=88, T__88=89, T__89=90, T__90=91, T__91=92, T__92=93, T__93=94, 
		T__94=95, Int=96, Uint=97, Byte=98, Fixed=99, Ufixed=100, VersionLiteral=101, 
		BooleanLiteral=102, DecimalNumber=103, HexNumber=104, NumberUnit=105, 
		HexLiteral=106, ReservedKeyword=107, AbstractKeyword=108, AnonymousKeyword=109, 
		BreakKeyword=110, ConstantKeyword=111, ContinueKeyword=112, ContractKeyword=113, 
		ExternalKeyword=114, ImmutableKeyword=115, IndexedKeyword=116, InterfaceKeyword=117, 
		InternalKeyword=118, LibraryKeyword=119, OverrideKeyword=120, PayableKeyword=121, 
		PrivateKeyword=122, PublicKeyword=123, PureKeyword=124, ViewKeyword=125, 
		VirtualKeyword=126, Identifier=127, StringLiteral=128, PLUS=129, MINUS=130, 
		MULT=131, DIV=132, MOD=133, LSL=134, LSR=135, AND=136, OR=137, TRUE=138, 
		FALSE=139, BAND=140, BOR=141, NOT=142, INC=143, DEC=144, WS=145, SPEC_COMMENT=146, 
		COMMENT=147, SPEC_LINE_COMMENT=148, LINE_COMMENT=149;
	public static final int
		RULE_sourceUnit = 0, RULE_pragmaDirective = 1, RULE_pragmaName = 2, RULE_pragmaValue = 3, 
		RULE_version = 4, RULE_versionOperator = 5, RULE_versionConstraint = 6, 
		RULE_importDeclaration = 7, RULE_importDirective = 8, RULE_contractDefinition = 9, 
		RULE_inheritanceSpecifier = 10, RULE_contractPart = 11, RULE_stateVariableDeclaration = 12, 
		RULE_usingForDeclaration = 13, RULE_structDefinition = 14, RULE_constructorDefinition = 15, 
		RULE_modifierDefinition = 16, RULE_modifierInvocation = 17, RULE_functionDefinition = 18, 
		RULE_returnParameters = 19, RULE_modifierList = 20, RULE_eventDefinition = 21, 
		RULE_enumValue = 22, RULE_enumDefinition = 23, RULE_specDefinition = 24, 
		RULE_specExpression = 25, RULE_parameterList = 26, RULE_parameter = 27, 
		RULE_eventParameterList = 28, RULE_eventParameter = 29, RULE_functionTypeParameterList = 30, 
		RULE_functionTypeParameter = 31, RULE_variableDeclaration = 32, RULE_typeName = 33, 
		RULE_userDefinedTypeName = 34, RULE_mapping = 35, RULE_functionTypeName = 36, 
		RULE_storageLocation = 37, RULE_stateMutability = 38, RULE_block = 39, 
		RULE_uncheckedBlock = 40, RULE_statement = 41, RULE_placeHolderStatement = 42, 
		RULE_expressionStatement = 43, RULE_ifStatement = 44, RULE_whileStatement = 45, 
		RULE_simpleStatement = 46, RULE_forStatement = 47, RULE_inlineAssemblyStatement = 48, 
		RULE_doWhileStatement = 49, RULE_continueStatement = 50, RULE_breakStatement = 51, 
		RULE_returnStatement = 52, RULE_throwStatement = 53, RULE_emitStatement = 54, 
		RULE_variableDeclarationStatement = 55, RULE_variableDeclarationList = 56, 
		RULE_identifierList = 57, RULE_elementaryTypeName = 58, RULE_expression = 59, 
		RULE_primaryExpression = 60, RULE_minMaxTypeExpression = 61, RULE_expressionList = 62, 
		RULE_nameValueList = 63, RULE_nameValue = 64, RULE_functionCallArguments = 65, 
		RULE_functionCall = 66, RULE_assemblyBlock = 67, RULE_assemblyItem = 68, 
		RULE_assemblyExpression = 69, RULE_assemblyCall = 70, RULE_assemblyLocalDefinition = 71, 
		RULE_assemblyAssignment = 72, RULE_assemblyIdentifierOrList = 73, RULE_assemblyIdentifierList = 74, 
		RULE_assemblyStackAssignment = 75, RULE_labelDefinition = 76, RULE_assemblySwitch = 77, 
		RULE_assemblyCase = 78, RULE_assemblyFunctionDefinition = 79, RULE_assemblyFunctionReturns = 80, 
		RULE_assemblyFor = 81, RULE_assemblyIf = 82, RULE_assemblyLiteral = 83, 
		RULE_subAssembly = 84, RULE_tupleExpression = 85, RULE_elementaryTypeNameExpression = 86, 
		RULE_numberLiteral = 87, RULE_identifier = 88;
	private static String[] makeRuleNames() {
		return new String[] {
			"sourceUnit", "pragmaDirective", "pragmaName", "pragmaValue", "version", 
			"versionOperator", "versionConstraint", "importDeclaration", "importDirective", 
			"contractDefinition", "inheritanceSpecifier", "contractPart", "stateVariableDeclaration", 
			"usingForDeclaration", "structDefinition", "constructorDefinition", "modifierDefinition", 
			"modifierInvocation", "functionDefinition", "returnParameters", "modifierList", 
			"eventDefinition", "enumValue", "enumDefinition", "specDefinition", "specExpression", 
			"parameterList", "parameter", "eventParameterList", "eventParameter", 
			"functionTypeParameterList", "functionTypeParameter", "variableDeclaration", 
			"typeName", "userDefinedTypeName", "mapping", "functionTypeName", "storageLocation", 
			"stateMutability", "block", "uncheckedBlock", "statement", "placeHolderStatement", 
			"expressionStatement", "ifStatement", "whileStatement", "simpleStatement", 
			"forStatement", "inlineAssemblyStatement", "doWhileStatement", "continueStatement", 
			"breakStatement", "returnStatement", "throwStatement", "emitStatement", 
			"variableDeclarationStatement", "variableDeclarationList", "identifierList", 
			"elementaryTypeName", "expression", "primaryExpression", "minMaxTypeExpression", 
			"expressionList", "nameValueList", "nameValue", "functionCallArguments", 
			"functionCall", "assemblyBlock", "assemblyItem", "assemblyExpression", 
			"assemblyCall", "assemblyLocalDefinition", "assemblyAssignment", "assemblyIdentifierOrList", 
			"assemblyIdentifierList", "assemblyStackAssignment", "labelDefinition", 
			"assemblySwitch", "assemblyCase", "assemblyFunctionDefinition", "assemblyFunctionReturns", 
			"assemblyFor", "assemblyIf", "assemblyLiteral", "subAssembly", "tupleExpression", 
			"elementaryTypeNameExpression", "numberLiteral", "identifier"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'pragma'", "';'", "'^'", "'~'", "'>='", "'>'", "'<'", "'<='", 
			"'='", "'as'", "'import'", "'from'", "'{'", "','", "'}'", "'is'", "'('", 
			"')'", "'using'", "'for'", "'struct'", "'constructor'", "'modifier'", 
			"'function'", "'returns'", "'event'", "'enum'", "'only_if'", "'assumes'", 
			"'on_success'", "'contract_invariant'", "'invariant_for'", "'assignable'", 
			"'observes_invariant_for'", "'['", "']'", "'.'", "'mapping'", "'=>'", 
			"'memory'", "'storage'", "'calldata'", "'unchecked'", "'_;'", "'if'", 
			"'else'", "'while'", "'assembly'", "'do'", "'return'", "'throw'", "'emit'", 
			"'var'", "'address'", "'address payable'", "'bool'", "'string'", "'byte'", 
			"'new'", "'after'", "'delete'", "'**'", "'=='", "'!='", "'?'", "':'", 
			"'|='", "'^='", "'&='", "'<<='", "'>>='", "'+='", "'-='", "'*='", "'/='", 
			"'%='", "'->'", "'<->'", "'<-'", "'\\forall'", "'\\exists'", "'net'", 
			"'gross_from'", "'gross_to'", "'\\old'", "'\\result'", "'type'", "'min'", 
			"'max'", "'let'", "':='", "'=:'", "'switch'", "'case'", "'default'", 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			"'abstract'", "'anonymous'", "'break'", "'constant'", "'continue'", "'contract'", 
			"'external'", "'immutable'", "'indexed'", "'interface'", "'internal'", 
			"'library'", "'override'", "'payable'", "'private'", "'public'", "'pure'", 
			"'view'", "'virtual'", null, null, "'+'", "'-'", "'*'", "'/'", "'%'", 
			"'<<'", "'>>'", "'&&'", "'||'", "'true'", "'false'", "'&'", "'|'", "'!'", 
			"'++'", "'--'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, null, null, null, null, null, null, 
			"Int", "Uint", "Byte", "Fixed", "Ufixed", "VersionLiteral", "BooleanLiteral", 
			"DecimalNumber", "HexNumber", "NumberUnit", "HexLiteral", "ReservedKeyword", 
			"AbstractKeyword", "AnonymousKeyword", "BreakKeyword", "ConstantKeyword", 
			"ContinueKeyword", "ContractKeyword", "ExternalKeyword", "ImmutableKeyword", 
			"IndexedKeyword", "InterfaceKeyword", "InternalKeyword", "LibraryKeyword", 
			"OverrideKeyword", "PayableKeyword", "PrivateKeyword", "PublicKeyword", 
			"PureKeyword", "ViewKeyword", "VirtualKeyword", "Identifier", "StringLiteral", 
			"PLUS", "MINUS", "MULT", "DIV", "MOD", "LSL", "LSR", "AND", "OR", "TRUE", 
			"FALSE", "BAND", "BOR", "NOT", "INC", "DEC", "WS", "SPEC_COMMENT", "COMMENT", 
			"SPEC_LINE_COMMENT", "LINE_COMMENT"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "Solidity.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public SolidityParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class SourceUnitContext extends ParserRuleContext {
		public TerminalNode EOF() { return getToken(SolidityParser.EOF, 0); }
		public List<PragmaDirectiveContext> pragmaDirective() {
			return getRuleContexts(PragmaDirectiveContext.class);
		}
		public PragmaDirectiveContext pragmaDirective(int i) {
			return getRuleContext(PragmaDirectiveContext.class,i);
		}
		public List<ImportDirectiveContext> importDirective() {
			return getRuleContexts(ImportDirectiveContext.class);
		}
		public ImportDirectiveContext importDirective(int i) {
			return getRuleContext(ImportDirectiveContext.class,i);
		}
		public List<ContractDefinitionContext> contractDefinition() {
			return getRuleContexts(ContractDefinitionContext.class);
		}
		public ContractDefinitionContext contractDefinition(int i) {
			return getRuleContext(ContractDefinitionContext.class,i);
		}
		public List<StructDefinitionContext> structDefinition() {
			return getRuleContexts(StructDefinitionContext.class);
		}
		public StructDefinitionContext structDefinition(int i) {
			return getRuleContext(StructDefinitionContext.class,i);
		}
		public SourceUnitContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_sourceUnit; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSourceUnit(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSourceUnit(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSourceUnit(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SourceUnitContext sourceUnit() throws RecognitionException {
		SourceUnitContext _localctx = new SourceUnitContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_sourceUnit);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(184);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__0) | (1L << T__10) | (1L << T__20))) != 0) || ((((_la - 108)) & ~0x3f) == 0 && ((1L << (_la - 108)) & ((1L << (AbstractKeyword - 108)) | (1L << (ContractKeyword - 108)) | (1L << (InterfaceKeyword - 108)) | (1L << (LibraryKeyword - 108)))) != 0)) {
				{
				setState(182);
				_errHandler.sync(this);
				switch (_input.LA(1)) {
				case T__0:
					{
					setState(178);
					pragmaDirective();
					}
					break;
				case T__10:
					{
					setState(179);
					importDirective();
					}
					break;
				case AbstractKeyword:
				case ContractKeyword:
				case InterfaceKeyword:
				case LibraryKeyword:
					{
					setState(180);
					contractDefinition();
					}
					break;
				case T__20:
					{
					setState(181);
					structDefinition();
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				}
				setState(186);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(187);
			match(EOF);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class PragmaDirectiveContext extends ParserRuleContext {
		public PragmaNameContext pragmaName() {
			return getRuleContext(PragmaNameContext.class,0);
		}
		public PragmaValueContext pragmaValue() {
			return getRuleContext(PragmaValueContext.class,0);
		}
		public PragmaDirectiveContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_pragmaDirective; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterPragmaDirective(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitPragmaDirective(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitPragmaDirective(this);
			else return visitor.visitChildren(this);
		}
	}

	public final PragmaDirectiveContext pragmaDirective() throws RecognitionException {
		PragmaDirectiveContext _localctx = new PragmaDirectiveContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_pragmaDirective);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(189);
			match(T__0);
			setState(190);
			pragmaName();
			setState(191);
			pragmaValue();
			setState(192);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class PragmaNameContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public PragmaNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_pragmaName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterPragmaName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitPragmaName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitPragmaName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final PragmaNameContext pragmaName() throws RecognitionException {
		PragmaNameContext _localctx = new PragmaNameContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_pragmaName);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(194);
			identifier();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class PragmaValueContext extends ParserRuleContext {
		public VersionContext version() {
			return getRuleContext(VersionContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public PragmaValueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_pragmaValue; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterPragmaValue(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitPragmaValue(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitPragmaValue(this);
			else return visitor.visitChildren(this);
		}
	}

	public final PragmaValueContext pragmaValue() throws RecognitionException {
		PragmaValueContext _localctx = new PragmaValueContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_pragmaValue);
		try {
			setState(198);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(196);
				version();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(197);
				expression(0);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VersionContext extends ParserRuleContext {
		public List<VersionConstraintContext> versionConstraint() {
			return getRuleContexts(VersionConstraintContext.class);
		}
		public VersionConstraintContext versionConstraint(int i) {
			return getRuleContext(VersionConstraintContext.class,i);
		}
		public VersionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_version; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterVersion(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitVersion(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitVersion(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VersionContext version() throws RecognitionException {
		VersionContext _localctx = new VersionContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_version);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(200);
			versionConstraint();
			setState(202);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__2) | (1L << T__3) | (1L << T__4) | (1L << T__5) | (1L << T__6) | (1L << T__7) | (1L << T__8))) != 0) || _la==VersionLiteral) {
				{
				setState(201);
				versionConstraint();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VersionOperatorContext extends ParserRuleContext {
		public VersionOperatorContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_versionOperator; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterVersionOperator(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitVersionOperator(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitVersionOperator(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VersionOperatorContext versionOperator() throws RecognitionException {
		VersionOperatorContext _localctx = new VersionOperatorContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_versionOperator);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(204);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__2) | (1L << T__3) | (1L << T__4) | (1L << T__5) | (1L << T__6) | (1L << T__7) | (1L << T__8))) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VersionConstraintContext extends ParserRuleContext {
		public TerminalNode VersionLiteral() { return getToken(SolidityParser.VersionLiteral, 0); }
		public VersionOperatorContext versionOperator() {
			return getRuleContext(VersionOperatorContext.class,0);
		}
		public VersionConstraintContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_versionConstraint; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterVersionConstraint(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitVersionConstraint(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitVersionConstraint(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VersionConstraintContext versionConstraint() throws RecognitionException {
		VersionConstraintContext _localctx = new VersionConstraintContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_versionConstraint);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(207);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__2) | (1L << T__3) | (1L << T__4) | (1L << T__5) | (1L << T__6) | (1L << T__7) | (1L << T__8))) != 0)) {
				{
				setState(206);
				versionOperator();
				}
			}

			setState(209);
			match(VersionLiteral);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ImportDeclarationContext extends ParserRuleContext {
		public List<IdentifierContext> identifier() {
			return getRuleContexts(IdentifierContext.class);
		}
		public IdentifierContext identifier(int i) {
			return getRuleContext(IdentifierContext.class,i);
		}
		public ImportDeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_importDeclaration; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterImportDeclaration(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitImportDeclaration(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitImportDeclaration(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ImportDeclarationContext importDeclaration() throws RecognitionException {
		ImportDeclarationContext _localctx = new ImportDeclarationContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_importDeclaration);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(211);
			identifier();
			setState(214);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__9) {
				{
				setState(212);
				match(T__9);
				setState(213);
				identifier();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ImportDirectiveContext extends ParserRuleContext {
		public TerminalNode StringLiteral() { return getToken(SolidityParser.StringLiteral, 0); }
		public List<IdentifierContext> identifier() {
			return getRuleContexts(IdentifierContext.class);
		}
		public IdentifierContext identifier(int i) {
			return getRuleContext(IdentifierContext.class,i);
		}
		public TerminalNode MULT() { return getToken(SolidityParser.MULT, 0); }
		public List<ImportDeclarationContext> importDeclaration() {
			return getRuleContexts(ImportDeclarationContext.class);
		}
		public ImportDeclarationContext importDeclaration(int i) {
			return getRuleContext(ImportDeclarationContext.class,i);
		}
		public ImportDirectiveContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_importDirective; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterImportDirective(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitImportDirective(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitImportDirective(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ImportDirectiveContext importDirective() throws RecognitionException {
		ImportDirectiveContext _localctx = new ImportDirectiveContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_importDirective);
		int _la;
		try {
			setState(250);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,10,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(216);
				match(T__10);
				setState(217);
				match(StringLiteral);
				setState(220);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__9) {
					{
					setState(218);
					match(T__9);
					setState(219);
					identifier();
					}
				}

				setState(222);
				match(T__1);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(223);
				match(T__10);
				setState(226);
				_errHandler.sync(this);
				switch (_input.LA(1)) {
				case MULT:
					{
					setState(224);
					match(MULT);
					}
					break;
				case T__11:
				case Identifier:
					{
					setState(225);
					identifier();
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				setState(230);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__9) {
					{
					setState(228);
					match(T__9);
					setState(229);
					identifier();
					}
				}

				setState(232);
				match(T__11);
				setState(233);
				match(StringLiteral);
				setState(234);
				match(T__1);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(235);
				match(T__10);
				setState(236);
				match(T__12);
				setState(237);
				importDeclaration();
				setState(242);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__13) {
					{
					{
					setState(238);
					match(T__13);
					setState(239);
					importDeclaration();
					}
					}
					setState(244);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(245);
				match(T__14);
				setState(246);
				match(T__11);
				setState(247);
				match(StringLiteral);
				setState(248);
				match(T__1);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ContractDefinitionContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public TerminalNode ContractKeyword() { return getToken(SolidityParser.ContractKeyword, 0); }
		public TerminalNode InterfaceKeyword() { return getToken(SolidityParser.InterfaceKeyword, 0); }
		public TerminalNode LibraryKeyword() { return getToken(SolidityParser.LibraryKeyword, 0); }
		public TerminalNode AbstractKeyword() { return getToken(SolidityParser.AbstractKeyword, 0); }
		public List<InheritanceSpecifierContext> inheritanceSpecifier() {
			return getRuleContexts(InheritanceSpecifierContext.class);
		}
		public InheritanceSpecifierContext inheritanceSpecifier(int i) {
			return getRuleContext(InheritanceSpecifierContext.class,i);
		}
		public List<ContractPartContext> contractPart() {
			return getRuleContexts(ContractPartContext.class);
		}
		public ContractPartContext contractPart(int i) {
			return getRuleContext(ContractPartContext.class,i);
		}
		public ContractDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_contractDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterContractDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitContractDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitContractDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ContractDefinitionContext contractDefinition() throws RecognitionException {
		ContractDefinitionContext _localctx = new ContractDefinitionContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_contractDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(253);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==AbstractKeyword) {
				{
				setState(252);
				match(AbstractKeyword);
				}
			}

			setState(255);
			_la = _input.LA(1);
			if ( !(((((_la - 113)) & ~0x3f) == 0 && ((1L << (_la - 113)) & ((1L << (ContractKeyword - 113)) | (1L << (InterfaceKeyword - 113)) | (1L << (LibraryKeyword - 113)))) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			setState(256);
			identifier();
			setState(266);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__15) {
				{
				setState(257);
				match(T__15);
				setState(258);
				inheritanceSpecifier();
				setState(263);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__13) {
					{
					{
					setState(259);
					match(T__13);
					setState(260);
					inheritanceSpecifier();
					}
					}
					setState(265);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(268);
			match(T__12);
			setState(272);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__18) | (1L << T__20) | (1L << T__21) | (1L << T__22) | (1L << T__23) | (1L << T__25) | (1L << T__26) | (1L << T__37) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57))) != 0) || ((((_la - 96)) & ~0x3f) == 0 && ((1L << (_la - 96)) & ((1L << (Int - 96)) | (1L << (Uint - 96)) | (1L << (Byte - 96)) | (1L << (Fixed - 96)) | (1L << (Ufixed - 96)) | (1L << (Identifier - 96)))) != 0)) {
				{
				{
				setState(269);
				contractPart();
				}
				}
				setState(274);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(275);
			match(T__14);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class InheritanceSpecifierContext extends ParserRuleContext {
		public UserDefinedTypeNameContext userDefinedTypeName() {
			return getRuleContext(UserDefinedTypeNameContext.class,0);
		}
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public InheritanceSpecifierContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_inheritanceSpecifier; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterInheritanceSpecifier(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitInheritanceSpecifier(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitInheritanceSpecifier(this);
			else return visitor.visitChildren(this);
		}
	}

	public final InheritanceSpecifierContext inheritanceSpecifier() throws RecognitionException {
		InheritanceSpecifierContext _localctx = new InheritanceSpecifierContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_inheritanceSpecifier);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(277);
			userDefinedTypeName();
			setState(289);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__16) {
				{
				setState(278);
				match(T__16);
				setState(279);
				expression(0);
				setState(284);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__13) {
					{
					{
					setState(280);
					match(T__13);
					setState(281);
					expression(0);
					}
					}
					setState(286);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(287);
				match(T__17);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ContractPartContext extends ParserRuleContext {
		public StateVariableDeclarationContext stateVariableDeclaration() {
			return getRuleContext(StateVariableDeclarationContext.class,0);
		}
		public UsingForDeclarationContext usingForDeclaration() {
			return getRuleContext(UsingForDeclarationContext.class,0);
		}
		public StructDefinitionContext structDefinition() {
			return getRuleContext(StructDefinitionContext.class,0);
		}
		public ConstructorDefinitionContext constructorDefinition() {
			return getRuleContext(ConstructorDefinitionContext.class,0);
		}
		public ModifierDefinitionContext modifierDefinition() {
			return getRuleContext(ModifierDefinitionContext.class,0);
		}
		public FunctionDefinitionContext functionDefinition() {
			return getRuleContext(FunctionDefinitionContext.class,0);
		}
		public EventDefinitionContext eventDefinition() {
			return getRuleContext(EventDefinitionContext.class,0);
		}
		public EnumDefinitionContext enumDefinition() {
			return getRuleContext(EnumDefinitionContext.class,0);
		}
		public ContractPartContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_contractPart; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterContractPart(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitContractPart(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitContractPart(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ContractPartContext contractPart() throws RecognitionException {
		ContractPartContext _localctx = new ContractPartContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_contractPart);
		try {
			setState(299);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,17,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(291);
				stateVariableDeclaration();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(292);
				usingForDeclaration();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(293);
				structDefinition();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(294);
				constructorDefinition();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(295);
				modifierDefinition();
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(296);
				functionDefinition();
				}
				break;
			case 7:
				enterOuterAlt(_localctx, 7);
				{
				setState(297);
				eventDefinition();
				}
				break;
			case 8:
				enterOuterAlt(_localctx, 8);
				{
				setState(298);
				enumDefinition();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StateVariableDeclarationContext extends ParserRuleContext {
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public List<TerminalNode> PublicKeyword() { return getTokens(SolidityParser.PublicKeyword); }
		public TerminalNode PublicKeyword(int i) {
			return getToken(SolidityParser.PublicKeyword, i);
		}
		public List<TerminalNode> InternalKeyword() { return getTokens(SolidityParser.InternalKeyword); }
		public TerminalNode InternalKeyword(int i) {
			return getToken(SolidityParser.InternalKeyword, i);
		}
		public List<TerminalNode> PrivateKeyword() { return getTokens(SolidityParser.PrivateKeyword); }
		public TerminalNode PrivateKeyword(int i) {
			return getToken(SolidityParser.PrivateKeyword, i);
		}
		public List<TerminalNode> ConstantKeyword() { return getTokens(SolidityParser.ConstantKeyword); }
		public TerminalNode ConstantKeyword(int i) {
			return getToken(SolidityParser.ConstantKeyword, i);
		}
		public List<TerminalNode> ImmutableKeyword() { return getTokens(SolidityParser.ImmutableKeyword); }
		public TerminalNode ImmutableKeyword(int i) {
			return getToken(SolidityParser.ImmutableKeyword, i);
		}
		public StateVariableDeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_stateVariableDeclaration; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterStateVariableDeclaration(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitStateVariableDeclaration(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitStateVariableDeclaration(this);
			else return visitor.visitChildren(this);
		}
	}

	public final StateVariableDeclarationContext stateVariableDeclaration() throws RecognitionException {
		StateVariableDeclarationContext _localctx = new StateVariableDeclarationContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_stateVariableDeclaration);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(301);
			typeName(0);
			setState(305);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (((((_la - 111)) & ~0x3f) == 0 && ((1L << (_la - 111)) & ((1L << (ConstantKeyword - 111)) | (1L << (ImmutableKeyword - 111)) | (1L << (InternalKeyword - 111)) | (1L << (PrivateKeyword - 111)) | (1L << (PublicKeyword - 111)))) != 0)) {
				{
				{
				setState(302);
				_la = _input.LA(1);
				if ( !(((((_la - 111)) & ~0x3f) == 0 && ((1L << (_la - 111)) & ((1L << (ConstantKeyword - 111)) | (1L << (ImmutableKeyword - 111)) | (1L << (InternalKeyword - 111)) | (1L << (PrivateKeyword - 111)) | (1L << (PublicKeyword - 111)))) != 0)) ) {
				_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				}
				}
				setState(307);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(308);
			identifier();
			setState(311);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__8) {
				{
				setState(309);
				match(T__8);
				setState(310);
				expression(0);
				}
			}

			setState(313);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class UsingForDeclarationContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public TerminalNode MULT() { return getToken(SolidityParser.MULT, 0); }
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public UsingForDeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_usingForDeclaration; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterUsingForDeclaration(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitUsingForDeclaration(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitUsingForDeclaration(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UsingForDeclarationContext usingForDeclaration() throws RecognitionException {
		UsingForDeclarationContext _localctx = new UsingForDeclarationContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_usingForDeclaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(315);
			match(T__18);
			setState(316);
			identifier();
			setState(317);
			match(T__19);
			setState(320);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case MULT:
				{
				setState(318);
				match(MULT);
				}
				break;
			case T__11:
			case T__23:
			case T__37:
			case T__52:
			case T__53:
			case T__54:
			case T__55:
			case T__56:
			case T__57:
			case Int:
			case Uint:
			case Byte:
			case Fixed:
			case Ufixed:
			case Identifier:
				{
				setState(319);
				typeName(0);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			setState(322);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StructDefinitionContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public List<VariableDeclarationContext> variableDeclaration() {
			return getRuleContexts(VariableDeclarationContext.class);
		}
		public VariableDeclarationContext variableDeclaration(int i) {
			return getRuleContext(VariableDeclarationContext.class,i);
		}
		public StructDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_structDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterStructDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitStructDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitStructDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final StructDefinitionContext structDefinition() throws RecognitionException {
		StructDefinitionContext _localctx = new StructDefinitionContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_structDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(324);
			match(T__20);
			setState(325);
			identifier();
			setState(326);
			match(T__12);
			setState(337);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__23) | (1L << T__37) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57))) != 0) || ((((_la - 96)) & ~0x3f) == 0 && ((1L << (_la - 96)) & ((1L << (Int - 96)) | (1L << (Uint - 96)) | (1L << (Byte - 96)) | (1L << (Fixed - 96)) | (1L << (Ufixed - 96)) | (1L << (Identifier - 96)))) != 0)) {
				{
				setState(327);
				variableDeclaration();
				setState(328);
				match(T__1);
				setState(334);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__23) | (1L << T__37) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57))) != 0) || ((((_la - 96)) & ~0x3f) == 0 && ((1L << (_la - 96)) & ((1L << (Int - 96)) | (1L << (Uint - 96)) | (1L << (Byte - 96)) | (1L << (Fixed - 96)) | (1L << (Ufixed - 96)) | (1L << (Identifier - 96)))) != 0)) {
					{
					{
					setState(329);
					variableDeclaration();
					setState(330);
					match(T__1);
					}
					}
					setState(336);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(339);
			match(T__14);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ConstructorDefinitionContext extends ParserRuleContext {
		public ParameterListContext parameterList() {
			return getRuleContext(ParameterListContext.class,0);
		}
		public ModifierListContext modifierList() {
			return getRuleContext(ModifierListContext.class,0);
		}
		public BlockContext block() {
			return getRuleContext(BlockContext.class,0);
		}
		public ConstructorDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constructorDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterConstructorDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitConstructorDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitConstructorDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConstructorDefinitionContext constructorDefinition() throws RecognitionException {
		ConstructorDefinitionContext _localctx = new ConstructorDefinitionContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_constructorDefinition);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(341);
			match(T__21);
			setState(342);
			parameterList();
			setState(343);
			modifierList();
			setState(344);
			block();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ModifierDefinitionContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public BlockContext block() {
			return getRuleContext(BlockContext.class,0);
		}
		public ParameterListContext parameterList() {
			return getRuleContext(ParameterListContext.class,0);
		}
		public TerminalNode VirtualKeyword() { return getToken(SolidityParser.VirtualKeyword, 0); }
		public TerminalNode OverrideKeyword() { return getToken(SolidityParser.OverrideKeyword, 0); }
		public ModifierDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_modifierDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterModifierDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitModifierDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitModifierDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ModifierDefinitionContext modifierDefinition() throws RecognitionException {
		ModifierDefinitionContext _localctx = new ModifierDefinitionContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_modifierDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(346);
			match(T__22);
			setState(347);
			identifier();
			setState(349);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__16) {
				{
				setState(348);
				parameterList();
				}
			}

			setState(352);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==OverrideKeyword || _la==VirtualKeyword) {
				{
				setState(351);
				_la = _input.LA(1);
				if ( !(_la==OverrideKeyword || _la==VirtualKeyword) ) {
				_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				}
			}

			setState(354);
			block();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ModifierInvocationContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public ExpressionListContext expressionList() {
			return getRuleContext(ExpressionListContext.class,0);
		}
		public ModifierInvocationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_modifierInvocation; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterModifierInvocation(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitModifierInvocation(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitModifierInvocation(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ModifierInvocationContext modifierInvocation() throws RecognitionException {
		ModifierInvocationContext _localctx = new ModifierInvocationContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_modifierInvocation);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(356);
			identifier();
			setState(362);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__16) {
				{
				setState(357);
				match(T__16);
				setState(359);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__11) | (1L << T__16) | (1L << T__34) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57) | (1L << T__58) | (1L << T__59) | (1L << T__60))) != 0) || ((((_la - 82)) & ~0x3f) == 0 && ((1L << (_la - 82)) & ((1L << (T__81 - 82)) | (1L << (T__82 - 82)) | (1L << (T__83 - 82)) | (1L << (T__84 - 82)) | (1L << (T__85 - 82)) | (1L << (T__86 - 82)) | (1L << (Int - 82)) | (1L << (Uint - 82)) | (1L << (Byte - 82)) | (1L << (Fixed - 82)) | (1L << (Ufixed - 82)) | (1L << (BooleanLiteral - 82)) | (1L << (DecimalNumber - 82)) | (1L << (HexNumber - 82)) | (1L << (HexLiteral - 82)) | (1L << (Identifier - 82)) | (1L << (StringLiteral - 82)) | (1L << (PLUS - 82)) | (1L << (MINUS - 82)) | (1L << (NOT - 82)) | (1L << (INC - 82)) | (1L << (DEC - 82)))) != 0)) {
					{
					setState(358);
					expressionList();
					}
				}

				setState(361);
				match(T__17);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FunctionDefinitionContext extends ParserRuleContext {
		public ParameterListContext parameterList() {
			return getRuleContext(ParameterListContext.class,0);
		}
		public ModifierListContext modifierList() {
			return getRuleContext(ModifierListContext.class,0);
		}
		public BlockContext block() {
			return getRuleContext(BlockContext.class,0);
		}
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public ReturnParametersContext returnParameters() {
			return getRuleContext(ReturnParametersContext.class,0);
		}
		public FunctionDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_functionDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterFunctionDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitFunctionDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitFunctionDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FunctionDefinitionContext functionDefinition() throws RecognitionException {
		FunctionDefinitionContext _localctx = new FunctionDefinitionContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_functionDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(364);
			match(T__23);
			setState(366);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__11 || _la==Identifier) {
				{
				setState(365);
				identifier();
				}
			}

			setState(368);
			parameterList();
			setState(369);
			modifierList();
			setState(371);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__24) {
				{
				setState(370);
				returnParameters();
				}
			}

			setState(375);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__1:
				{
				setState(373);
				match(T__1);
				}
				break;
			case T__12:
				{
				setState(374);
				block();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ReturnParametersContext extends ParserRuleContext {
		public ParameterListContext parameterList() {
			return getRuleContext(ParameterListContext.class,0);
		}
		public ReturnParametersContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_returnParameters; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterReturnParameters(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitReturnParameters(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitReturnParameters(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ReturnParametersContext returnParameters() throws RecognitionException {
		ReturnParametersContext _localctx = new ReturnParametersContext(_ctx, getState());
		enterRule(_localctx, 38, RULE_returnParameters);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(377);
			match(T__24);
			setState(378);
			parameterList();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ModifierListContext extends ParserRuleContext {
		public List<ModifierInvocationContext> modifierInvocation() {
			return getRuleContexts(ModifierInvocationContext.class);
		}
		public ModifierInvocationContext modifierInvocation(int i) {
			return getRuleContext(ModifierInvocationContext.class,i);
		}
		public List<StateMutabilityContext> stateMutability() {
			return getRuleContexts(StateMutabilityContext.class);
		}
		public StateMutabilityContext stateMutability(int i) {
			return getRuleContext(StateMutabilityContext.class,i);
		}
		public List<TerminalNode> ExternalKeyword() { return getTokens(SolidityParser.ExternalKeyword); }
		public TerminalNode ExternalKeyword(int i) {
			return getToken(SolidityParser.ExternalKeyword, i);
		}
		public List<TerminalNode> PublicKeyword() { return getTokens(SolidityParser.PublicKeyword); }
		public TerminalNode PublicKeyword(int i) {
			return getToken(SolidityParser.PublicKeyword, i);
		}
		public List<TerminalNode> InternalKeyword() { return getTokens(SolidityParser.InternalKeyword); }
		public TerminalNode InternalKeyword(int i) {
			return getToken(SolidityParser.InternalKeyword, i);
		}
		public List<TerminalNode> PrivateKeyword() { return getTokens(SolidityParser.PrivateKeyword); }
		public TerminalNode PrivateKeyword(int i) {
			return getToken(SolidityParser.PrivateKeyword, i);
		}
		public List<TerminalNode> VirtualKeyword() { return getTokens(SolidityParser.VirtualKeyword); }
		public TerminalNode VirtualKeyword(int i) {
			return getToken(SolidityParser.VirtualKeyword, i);
		}
		public List<TerminalNode> OverrideKeyword() { return getTokens(SolidityParser.OverrideKeyword); }
		public TerminalNode OverrideKeyword(int i) {
			return getToken(SolidityParser.OverrideKeyword, i);
		}
		public ModifierListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_modifierList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterModifierList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitModifierList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitModifierList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ModifierListContext modifierList() throws RecognitionException {
		ModifierListContext _localctx = new ModifierListContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_modifierList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(390);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__11 || ((((_la - 111)) & ~0x3f) == 0 && ((1L << (_la - 111)) & ((1L << (ConstantKeyword - 111)) | (1L << (ExternalKeyword - 111)) | (1L << (InternalKeyword - 111)) | (1L << (OverrideKeyword - 111)) | (1L << (PayableKeyword - 111)) | (1L << (PrivateKeyword - 111)) | (1L << (PublicKeyword - 111)) | (1L << (PureKeyword - 111)) | (1L << (ViewKeyword - 111)) | (1L << (VirtualKeyword - 111)) | (1L << (Identifier - 111)))) != 0)) {
				{
				setState(388);
				_errHandler.sync(this);
				switch (_input.LA(1)) {
				case T__11:
				case Identifier:
					{
					setState(380);
					modifierInvocation();
					}
					break;
				case ConstantKeyword:
				case PayableKeyword:
				case PureKeyword:
				case ViewKeyword:
					{
					setState(381);
					stateMutability();
					}
					break;
				case ExternalKeyword:
					{
					setState(382);
					match(ExternalKeyword);
					}
					break;
				case PublicKeyword:
					{
					setState(383);
					match(PublicKeyword);
					}
					break;
				case InternalKeyword:
					{
					setState(384);
					match(InternalKeyword);
					}
					break;
				case PrivateKeyword:
					{
					setState(385);
					match(PrivateKeyword);
					}
					break;
				case VirtualKeyword:
					{
					setState(386);
					match(VirtualKeyword);
					}
					break;
				case OverrideKeyword:
					{
					setState(387);
					match(OverrideKeyword);
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				}
				setState(392);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EventDefinitionContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public EventParameterListContext eventParameterList() {
			return getRuleContext(EventParameterListContext.class,0);
		}
		public TerminalNode AnonymousKeyword() { return getToken(SolidityParser.AnonymousKeyword, 0); }
		public EventDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_eventDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterEventDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitEventDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitEventDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final EventDefinitionContext eventDefinition() throws RecognitionException {
		EventDefinitionContext _localctx = new EventDefinitionContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_eventDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(393);
			match(T__25);
			setState(394);
			identifier();
			setState(395);
			eventParameterList();
			setState(397);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==AnonymousKeyword) {
				{
				setState(396);
				match(AnonymousKeyword);
				}
			}

			setState(399);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EnumValueContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public EnumValueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_enumValue; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterEnumValue(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitEnumValue(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitEnumValue(this);
			else return visitor.visitChildren(this);
		}
	}

	public final EnumValueContext enumValue() throws RecognitionException {
		EnumValueContext _localctx = new EnumValueContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_enumValue);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(401);
			identifier();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EnumDefinitionContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public List<EnumValueContext> enumValue() {
			return getRuleContexts(EnumValueContext.class);
		}
		public EnumValueContext enumValue(int i) {
			return getRuleContext(EnumValueContext.class,i);
		}
		public EnumDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_enumDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterEnumDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitEnumDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitEnumDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final EnumDefinitionContext enumDefinition() throws RecognitionException {
		EnumDefinitionContext _localctx = new EnumDefinitionContext(_ctx, getState());
		enterRule(_localctx, 46, RULE_enumDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(403);
			match(T__26);
			setState(404);
			identifier();
			setState(405);
			match(T__12);
			setState(407);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__11 || _la==Identifier) {
				{
				setState(406);
				enumValue();
				}
			}

			setState(413);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__13) {
				{
				{
				setState(409);
				match(T__13);
				setState(410);
				enumValue();
				}
				}
				setState(415);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(416);
			match(T__14);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SpecDefinitionContext extends ParserRuleContext {
		public List<SpecExpressionContext> specExpression() {
			return getRuleContexts(SpecExpressionContext.class);
		}
		public SpecExpressionContext specExpression(int i) {
			return getRuleContext(SpecExpressionContext.class,i);
		}
		public SpecDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_specDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSpecDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSpecDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSpecDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SpecDefinitionContext specDefinition() throws RecognitionException {
		SpecDefinitionContext _localctx = new SpecDefinitionContext(_ctx, getState());
		enterRule(_localctx, 48, RULE_specDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(421);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__27) | (1L << T__28) | (1L << T__29) | (1L << T__30) | (1L << T__31) | (1L << T__32))) != 0) || _la==Identifier) {
				{
				{
				setState(418);
				specExpression();
				}
				}
				setState(423);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SpecExpressionContext extends ParserRuleContext {
		public SpecExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_specExpression; }
	 
		public SpecExpressionContext() { }
		public void copyFrom(SpecExpressionContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class SpecAssumesContext extends SpecExpressionContext {
		public ExpressionStatementContext expressionStatement() {
			return getRuleContext(ExpressionStatementContext.class,0);
		}
		public SpecAssumesContext(SpecExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSpecAssumes(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSpecAssumes(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSpecAssumes(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class SpecObservesInvariantForContext extends SpecExpressionContext {
		public List<IdentifierContext> identifier() {
			return getRuleContexts(IdentifierContext.class);
		}
		public IdentifierContext identifier(int i) {
			return getRuleContext(IdentifierContext.class,i);
		}
		public SpecObservesInvariantForContext(SpecExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSpecObservesInvariantFor(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSpecObservesInvariantFor(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSpecObservesInvariantFor(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class SpecContractInvariantContext extends SpecExpressionContext {
		public ExpressionStatementContext expressionStatement() {
			return getRuleContext(ExpressionStatementContext.class,0);
		}
		public SpecContractInvariantContext(SpecExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSpecContractInvariant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSpecContractInvariant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSpecContractInvariant(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class SpecAssignableContext extends SpecExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public SpecAssignableContext(SpecExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSpecAssignable(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSpecAssignable(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSpecAssignable(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class SpecOnlyIfContext extends SpecExpressionContext {
		public ExpressionStatementContext expressionStatement() {
			return getRuleContext(ExpressionStatementContext.class,0);
		}
		public SpecOnlyIfContext(SpecExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSpecOnlyIf(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSpecOnlyIf(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSpecOnlyIf(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class SpecLibraryInvariantContext extends SpecExpressionContext {
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public TerminalNode Identifier() { return getToken(SolidityParser.Identifier, 0); }
		public ExpressionStatementContext expressionStatement() {
			return getRuleContext(ExpressionStatementContext.class,0);
		}
		public SpecLibraryInvariantContext(SpecExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSpecLibraryInvariant(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSpecLibraryInvariant(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSpecLibraryInvariant(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class SpecOnSuccessContext extends SpecExpressionContext {
		public ExpressionStatementContext expressionStatement() {
			return getRuleContext(ExpressionStatementContext.class,0);
		}
		public SpecOnSuccessContext(SpecExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSpecOnSuccess(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSpecOnSuccess(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSpecOnSuccess(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SpecExpressionContext specExpression() throws RecognitionException {
		SpecExpressionContext _localctx = new SpecExpressionContext(_ctx, getState());
		enterRule(_localctx, 50, RULE_specExpression);
		int _la;
		try {
			setState(452);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__27:
				_localctx = new SpecOnlyIfContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(424);
				match(T__27);
				setState(425);
				expressionStatement();
				}
				break;
			case T__28:
				_localctx = new SpecAssumesContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(426);
				match(T__28);
				setState(427);
				expressionStatement();
				}
				break;
			case T__29:
				_localctx = new SpecOnSuccessContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(428);
				match(T__29);
				setState(429);
				expressionStatement();
				}
				break;
			case T__30:
				_localctx = new SpecContractInvariantContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(430);
				match(T__30);
				setState(431);
				expressionStatement();
				}
				break;
			case T__31:
				_localctx = new SpecLibraryInvariantContext(_localctx);
				enterOuterAlt(_localctx, 5);
				{
				setState(432);
				match(T__31);
				setState(433);
				typeName(0);
				setState(434);
				match(Identifier);
				setState(435);
				match(T__1);
				setState(436);
				expressionStatement();
				}
				break;
			case T__32:
				_localctx = new SpecAssignableContext(_localctx);
				enterOuterAlt(_localctx, 6);
				{
				setState(438);
				match(T__32);
				setState(439);
				expression(0);
				setState(444);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__13) {
					{
					{
					setState(440);
					match(T__13);
					setState(441);
					expression(0);
					}
					}
					setState(446);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
				break;
			case T__11:
			case Identifier:
				_localctx = new SpecObservesInvariantForContext(_localctx);
				enterOuterAlt(_localctx, 7);
				{
				setState(447);
				identifier();
				setState(448);
				match(T__33);
				setState(449);
				identifier();
				setState(450);
				match(T__1);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ParameterListContext extends ParserRuleContext {
		public List<ParameterContext> parameter() {
			return getRuleContexts(ParameterContext.class);
		}
		public ParameterContext parameter(int i) {
			return getRuleContext(ParameterContext.class,i);
		}
		public ParameterListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_parameterList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterParameterList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitParameterList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitParameterList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ParameterListContext parameterList() throws RecognitionException {
		ParameterListContext _localctx = new ParameterListContext(_ctx, getState());
		enterRule(_localctx, 52, RULE_parameterList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(454);
			match(T__16);
			setState(463);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__23) | (1L << T__37) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57))) != 0) || ((((_la - 96)) & ~0x3f) == 0 && ((1L << (_la - 96)) & ((1L << (Int - 96)) | (1L << (Uint - 96)) | (1L << (Byte - 96)) | (1L << (Fixed - 96)) | (1L << (Ufixed - 96)) | (1L << (Identifier - 96)))) != 0)) {
				{
				setState(455);
				parameter();
				setState(460);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__13) {
					{
					{
					setState(456);
					match(T__13);
					setState(457);
					parameter();
					}
					}
					setState(462);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(465);
			match(T__17);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ParameterContext extends ParserRuleContext {
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public StorageLocationContext storageLocation() {
			return getRuleContext(StorageLocationContext.class,0);
		}
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public ParameterContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_parameter; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterParameter(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitParameter(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitParameter(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ParameterContext parameter() throws RecognitionException {
		ParameterContext _localctx = new ParameterContext(_ctx, getState());
		enterRule(_localctx, 54, RULE_parameter);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(467);
			typeName(0);
			setState(469);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__39) | (1L << T__40) | (1L << T__41))) != 0)) {
				{
				setState(468);
				storageLocation();
				}
			}

			setState(472);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__11 || _la==Identifier) {
				{
				setState(471);
				identifier();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EventParameterListContext extends ParserRuleContext {
		public List<EventParameterContext> eventParameter() {
			return getRuleContexts(EventParameterContext.class);
		}
		public EventParameterContext eventParameter(int i) {
			return getRuleContext(EventParameterContext.class,i);
		}
		public EventParameterListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_eventParameterList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterEventParameterList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitEventParameterList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitEventParameterList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final EventParameterListContext eventParameterList() throws RecognitionException {
		EventParameterListContext _localctx = new EventParameterListContext(_ctx, getState());
		enterRule(_localctx, 56, RULE_eventParameterList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(474);
			match(T__16);
			setState(483);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__23) | (1L << T__37) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57))) != 0) || ((((_la - 96)) & ~0x3f) == 0 && ((1L << (_la - 96)) & ((1L << (Int - 96)) | (1L << (Uint - 96)) | (1L << (Byte - 96)) | (1L << (Fixed - 96)) | (1L << (Ufixed - 96)) | (1L << (Identifier - 96)))) != 0)) {
				{
				setState(475);
				eventParameter();
				setState(480);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__13) {
					{
					{
					setState(476);
					match(T__13);
					setState(477);
					eventParameter();
					}
					}
					setState(482);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(485);
			match(T__17);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EventParameterContext extends ParserRuleContext {
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public TerminalNode IndexedKeyword() { return getToken(SolidityParser.IndexedKeyword, 0); }
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public EventParameterContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_eventParameter; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterEventParameter(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitEventParameter(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitEventParameter(this);
			else return visitor.visitChildren(this);
		}
	}

	public final EventParameterContext eventParameter() throws RecognitionException {
		EventParameterContext _localctx = new EventParameterContext(_ctx, getState());
		enterRule(_localctx, 58, RULE_eventParameter);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(487);
			typeName(0);
			setState(489);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==IndexedKeyword) {
				{
				setState(488);
				match(IndexedKeyword);
				}
			}

			setState(492);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__11 || _la==Identifier) {
				{
				setState(491);
				identifier();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FunctionTypeParameterListContext extends ParserRuleContext {
		public List<FunctionTypeParameterContext> functionTypeParameter() {
			return getRuleContexts(FunctionTypeParameterContext.class);
		}
		public FunctionTypeParameterContext functionTypeParameter(int i) {
			return getRuleContext(FunctionTypeParameterContext.class,i);
		}
		public FunctionTypeParameterListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_functionTypeParameterList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterFunctionTypeParameterList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitFunctionTypeParameterList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitFunctionTypeParameterList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FunctionTypeParameterListContext functionTypeParameterList() throws RecognitionException {
		FunctionTypeParameterListContext _localctx = new FunctionTypeParameterListContext(_ctx, getState());
		enterRule(_localctx, 60, RULE_functionTypeParameterList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(494);
			match(T__16);
			setState(503);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__23) | (1L << T__37) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57))) != 0) || ((((_la - 96)) & ~0x3f) == 0 && ((1L << (_la - 96)) & ((1L << (Int - 96)) | (1L << (Uint - 96)) | (1L << (Byte - 96)) | (1L << (Fixed - 96)) | (1L << (Ufixed - 96)) | (1L << (Identifier - 96)))) != 0)) {
				{
				setState(495);
				functionTypeParameter();
				setState(500);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__13) {
					{
					{
					setState(496);
					match(T__13);
					setState(497);
					functionTypeParameter();
					}
					}
					setState(502);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(505);
			match(T__17);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FunctionTypeParameterContext extends ParserRuleContext {
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public StorageLocationContext storageLocation() {
			return getRuleContext(StorageLocationContext.class,0);
		}
		public FunctionTypeParameterContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_functionTypeParameter; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterFunctionTypeParameter(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitFunctionTypeParameter(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitFunctionTypeParameter(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FunctionTypeParameterContext functionTypeParameter() throws RecognitionException {
		FunctionTypeParameterContext _localctx = new FunctionTypeParameterContext(_ctx, getState());
		enterRule(_localctx, 62, RULE_functionTypeParameter);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(507);
			typeName(0);
			setState(509);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__39) | (1L << T__40) | (1L << T__41))) != 0)) {
				{
				setState(508);
				storageLocation();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VariableDeclarationContext extends ParserRuleContext {
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public StorageLocationContext storageLocation() {
			return getRuleContext(StorageLocationContext.class,0);
		}
		public TerminalNode ConstantKeyword() { return getToken(SolidityParser.ConstantKeyword, 0); }
		public VariableDeclarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_variableDeclaration; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterVariableDeclaration(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitVariableDeclaration(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitVariableDeclaration(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VariableDeclarationContext variableDeclaration() throws RecognitionException {
		VariableDeclarationContext _localctx = new VariableDeclarationContext(_ctx, getState());
		enterRule(_localctx, 64, RULE_variableDeclaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(511);
			typeName(0);
			setState(514);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__39:
			case T__40:
			case T__41:
				{
				setState(512);
				storageLocation();
				}
				break;
			case ConstantKeyword:
				{
				setState(513);
				match(ConstantKeyword);
				}
				break;
			case T__11:
			case Identifier:
				break;
			default:
				break;
			}
			setState(516);
			identifier();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TypeNameContext extends ParserRuleContext {
		public ElementaryTypeNameContext elementaryTypeName() {
			return getRuleContext(ElementaryTypeNameContext.class,0);
		}
		public UserDefinedTypeNameContext userDefinedTypeName() {
			return getRuleContext(UserDefinedTypeNameContext.class,0);
		}
		public MappingContext mapping() {
			return getRuleContext(MappingContext.class,0);
		}
		public FunctionTypeNameContext functionTypeName() {
			return getRuleContext(FunctionTypeNameContext.class,0);
		}
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public TypeNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typeName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterTypeName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitTypeName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitTypeName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeNameContext typeName() throws RecognitionException {
		return typeName(0);
	}

	private TypeNameContext typeName(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		TypeNameContext _localctx = new TypeNameContext(_ctx, _parentState);
		TypeNameContext _prevctx = _localctx;
		int _startState = 66;
		enterRecursionRule(_localctx, 66, RULE_typeName, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(523);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__52:
			case T__53:
			case T__54:
			case T__55:
			case T__56:
			case T__57:
			case Int:
			case Uint:
			case Byte:
			case Fixed:
			case Ufixed:
				{
				setState(519);
				elementaryTypeName();
				}
				break;
			case T__11:
			case Identifier:
				{
				setState(520);
				userDefinedTypeName();
				}
				break;
			case T__37:
				{
				setState(521);
				mapping();
				}
				break;
			case T__23:
				{
				setState(522);
				functionTypeName();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(533);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,52,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new TypeNameContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_typeName);
					setState(525);
					if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
					setState(526);
					match(T__34);
					setState(528);
					_errHandler.sync(this);
					_la = _input.LA(1);
					if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__11) | (1L << T__16) | (1L << T__34) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57) | (1L << T__58) | (1L << T__59) | (1L << T__60))) != 0) || ((((_la - 82)) & ~0x3f) == 0 && ((1L << (_la - 82)) & ((1L << (T__81 - 82)) | (1L << (T__82 - 82)) | (1L << (T__83 - 82)) | (1L << (T__84 - 82)) | (1L << (T__85 - 82)) | (1L << (T__86 - 82)) | (1L << (Int - 82)) | (1L << (Uint - 82)) | (1L << (Byte - 82)) | (1L << (Fixed - 82)) | (1L << (Ufixed - 82)) | (1L << (BooleanLiteral - 82)) | (1L << (DecimalNumber - 82)) | (1L << (HexNumber - 82)) | (1L << (HexLiteral - 82)) | (1L << (Identifier - 82)) | (1L << (StringLiteral - 82)) | (1L << (PLUS - 82)) | (1L << (MINUS - 82)) | (1L << (NOT - 82)) | (1L << (INC - 82)) | (1L << (DEC - 82)))) != 0)) {
						{
						setState(527);
						expression(0);
						}
					}

					setState(530);
					match(T__35);
					}
					} 
				}
				setState(535);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,52,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class UserDefinedTypeNameContext extends ParserRuleContext {
		public List<IdentifierContext> identifier() {
			return getRuleContexts(IdentifierContext.class);
		}
		public IdentifierContext identifier(int i) {
			return getRuleContext(IdentifierContext.class,i);
		}
		public UserDefinedTypeNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_userDefinedTypeName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterUserDefinedTypeName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitUserDefinedTypeName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitUserDefinedTypeName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UserDefinedTypeNameContext userDefinedTypeName() throws RecognitionException {
		UserDefinedTypeNameContext _localctx = new UserDefinedTypeNameContext(_ctx, getState());
		enterRule(_localctx, 68, RULE_userDefinedTypeName);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(536);
			identifier();
			setState(541);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,53,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(537);
					match(T__36);
					setState(538);
					identifier();
					}
					} 
				}
				setState(543);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,53,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MappingContext extends ParserRuleContext {
		public ElementaryTypeNameContext elementaryTypeName() {
			return getRuleContext(ElementaryTypeNameContext.class,0);
		}
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public MappingContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_mapping; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterMapping(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitMapping(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitMapping(this);
			else return visitor.visitChildren(this);
		}
	}

	public final MappingContext mapping() throws RecognitionException {
		MappingContext _localctx = new MappingContext(_ctx, getState());
		enterRule(_localctx, 70, RULE_mapping);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(544);
			match(T__37);
			setState(545);
			match(T__16);
			setState(546);
			elementaryTypeName();
			setState(547);
			match(T__38);
			setState(548);
			typeName(0);
			setState(549);
			match(T__17);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FunctionTypeNameContext extends ParserRuleContext {
		public List<FunctionTypeParameterListContext> functionTypeParameterList() {
			return getRuleContexts(FunctionTypeParameterListContext.class);
		}
		public FunctionTypeParameterListContext functionTypeParameterList(int i) {
			return getRuleContext(FunctionTypeParameterListContext.class,i);
		}
		public List<TerminalNode> InternalKeyword() { return getTokens(SolidityParser.InternalKeyword); }
		public TerminalNode InternalKeyword(int i) {
			return getToken(SolidityParser.InternalKeyword, i);
		}
		public List<TerminalNode> ExternalKeyword() { return getTokens(SolidityParser.ExternalKeyword); }
		public TerminalNode ExternalKeyword(int i) {
			return getToken(SolidityParser.ExternalKeyword, i);
		}
		public List<StateMutabilityContext> stateMutability() {
			return getRuleContexts(StateMutabilityContext.class);
		}
		public StateMutabilityContext stateMutability(int i) {
			return getRuleContext(StateMutabilityContext.class,i);
		}
		public FunctionTypeNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_functionTypeName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterFunctionTypeName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitFunctionTypeName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitFunctionTypeName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FunctionTypeNameContext functionTypeName() throws RecognitionException {
		FunctionTypeNameContext _localctx = new FunctionTypeNameContext(_ctx, getState());
		enterRule(_localctx, 72, RULE_functionTypeName);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(551);
			match(T__23);
			setState(552);
			functionTypeParameterList();
			setState(558);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,55,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					setState(556);
					_errHandler.sync(this);
					switch (_input.LA(1)) {
					case InternalKeyword:
						{
						setState(553);
						match(InternalKeyword);
						}
						break;
					case ExternalKeyword:
						{
						setState(554);
						match(ExternalKeyword);
						}
						break;
					case ConstantKeyword:
					case PayableKeyword:
					case PureKeyword:
					case ViewKeyword:
						{
						setState(555);
						stateMutability();
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					} 
				}
				setState(560);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,55,_ctx);
			}
			setState(563);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,56,_ctx) ) {
			case 1:
				{
				setState(561);
				match(T__24);
				setState(562);
				functionTypeParameterList();
				}
				break;
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StorageLocationContext extends ParserRuleContext {
		public StorageLocationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_storageLocation; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterStorageLocation(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitStorageLocation(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitStorageLocation(this);
			else return visitor.visitChildren(this);
		}
	}

	public final StorageLocationContext storageLocation() throws RecognitionException {
		StorageLocationContext _localctx = new StorageLocationContext(_ctx, getState());
		enterRule(_localctx, 74, RULE_storageLocation);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(565);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__39) | (1L << T__40) | (1L << T__41))) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StateMutabilityContext extends ParserRuleContext {
		public TerminalNode PureKeyword() { return getToken(SolidityParser.PureKeyword, 0); }
		public TerminalNode ConstantKeyword() { return getToken(SolidityParser.ConstantKeyword, 0); }
		public TerminalNode ViewKeyword() { return getToken(SolidityParser.ViewKeyword, 0); }
		public TerminalNode PayableKeyword() { return getToken(SolidityParser.PayableKeyword, 0); }
		public StateMutabilityContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_stateMutability; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterStateMutability(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitStateMutability(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitStateMutability(this);
			else return visitor.visitChildren(this);
		}
	}

	public final StateMutabilityContext stateMutability() throws RecognitionException {
		StateMutabilityContext _localctx = new StateMutabilityContext(_ctx, getState());
		enterRule(_localctx, 76, RULE_stateMutability);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(567);
			_la = _input.LA(1);
			if ( !(((((_la - 111)) & ~0x3f) == 0 && ((1L << (_la - 111)) & ((1L << (ConstantKeyword - 111)) | (1L << (PayableKeyword - 111)) | (1L << (PureKeyword - 111)) | (1L << (ViewKeyword - 111)))) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BlockContext extends ParserRuleContext {
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public BlockContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_block; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterBlock(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitBlock(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitBlock(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BlockContext block() throws RecognitionException {
		BlockContext _localctx = new BlockContext(_ctx, getState());
		enterRule(_localctx, 78, RULE_block);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(569);
			match(T__12);
			setState(573);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__11) | (1L << T__12) | (1L << T__16) | (1L << T__19) | (1L << T__23) | (1L << T__34) | (1L << T__37) | (1L << T__42) | (1L << T__43) | (1L << T__44) | (1L << T__46) | (1L << T__47) | (1L << T__48) | (1L << T__49) | (1L << T__50) | (1L << T__51) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57) | (1L << T__58) | (1L << T__59) | (1L << T__60))) != 0) || ((((_la - 82)) & ~0x3f) == 0 && ((1L << (_la - 82)) & ((1L << (T__81 - 82)) | (1L << (T__82 - 82)) | (1L << (T__83 - 82)) | (1L << (T__84 - 82)) | (1L << (T__85 - 82)) | (1L << (T__86 - 82)) | (1L << (Int - 82)) | (1L << (Uint - 82)) | (1L << (Byte - 82)) | (1L << (Fixed - 82)) | (1L << (Ufixed - 82)) | (1L << (BooleanLiteral - 82)) | (1L << (DecimalNumber - 82)) | (1L << (HexNumber - 82)) | (1L << (HexLiteral - 82)) | (1L << (BreakKeyword - 82)) | (1L << (ContinueKeyword - 82)) | (1L << (Identifier - 82)) | (1L << (StringLiteral - 82)) | (1L << (PLUS - 82)) | (1L << (MINUS - 82)) | (1L << (NOT - 82)) | (1L << (INC - 82)) | (1L << (DEC - 82)))) != 0)) {
				{
				{
				setState(570);
				statement();
				}
				}
				setState(575);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(576);
			match(T__14);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class UncheckedBlockContext extends ParserRuleContext {
		public BlockContext block() {
			return getRuleContext(BlockContext.class,0);
		}
		public UncheckedBlockContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_uncheckedBlock; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterUncheckedBlock(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitUncheckedBlock(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitUncheckedBlock(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UncheckedBlockContext uncheckedBlock() throws RecognitionException {
		UncheckedBlockContext _localctx = new UncheckedBlockContext(_ctx, getState());
		enterRule(_localctx, 80, RULE_uncheckedBlock);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(578);
			match(T__42);
			setState(579);
			block();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StatementContext extends ParserRuleContext {
		public IfStatementContext ifStatement() {
			return getRuleContext(IfStatementContext.class,0);
		}
		public WhileStatementContext whileStatement() {
			return getRuleContext(WhileStatementContext.class,0);
		}
		public ForStatementContext forStatement() {
			return getRuleContext(ForStatementContext.class,0);
		}
		public BlockContext block() {
			return getRuleContext(BlockContext.class,0);
		}
		public UncheckedBlockContext uncheckedBlock() {
			return getRuleContext(UncheckedBlockContext.class,0);
		}
		public InlineAssemblyStatementContext inlineAssemblyStatement() {
			return getRuleContext(InlineAssemblyStatementContext.class,0);
		}
		public DoWhileStatementContext doWhileStatement() {
			return getRuleContext(DoWhileStatementContext.class,0);
		}
		public ContinueStatementContext continueStatement() {
			return getRuleContext(ContinueStatementContext.class,0);
		}
		public BreakStatementContext breakStatement() {
			return getRuleContext(BreakStatementContext.class,0);
		}
		public ReturnStatementContext returnStatement() {
			return getRuleContext(ReturnStatementContext.class,0);
		}
		public ThrowStatementContext throwStatement() {
			return getRuleContext(ThrowStatementContext.class,0);
		}
		public EmitStatementContext emitStatement() {
			return getRuleContext(EmitStatementContext.class,0);
		}
		public PlaceHolderStatementContext placeHolderStatement() {
			return getRuleContext(PlaceHolderStatementContext.class,0);
		}
		public SimpleStatementContext simpleStatement() {
			return getRuleContext(SimpleStatementContext.class,0);
		}
		public StatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final StatementContext statement() throws RecognitionException {
		StatementContext _localctx = new StatementContext(_ctx, getState());
		enterRule(_localctx, 82, RULE_statement);
		try {
			setState(595);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__44:
				enterOuterAlt(_localctx, 1);
				{
				setState(581);
				ifStatement();
				}
				break;
			case T__46:
				enterOuterAlt(_localctx, 2);
				{
				setState(582);
				whileStatement();
				}
				break;
			case T__19:
				enterOuterAlt(_localctx, 3);
				{
				setState(583);
				forStatement();
				}
				break;
			case T__12:
				enterOuterAlt(_localctx, 4);
				{
				setState(584);
				block();
				}
				break;
			case T__42:
				enterOuterAlt(_localctx, 5);
				{
				setState(585);
				uncheckedBlock();
				}
				break;
			case T__47:
				enterOuterAlt(_localctx, 6);
				{
				setState(586);
				inlineAssemblyStatement();
				}
				break;
			case T__48:
				enterOuterAlt(_localctx, 7);
				{
				setState(587);
				doWhileStatement();
				}
				break;
			case ContinueKeyword:
				enterOuterAlt(_localctx, 8);
				{
				setState(588);
				continueStatement();
				}
				break;
			case BreakKeyword:
				enterOuterAlt(_localctx, 9);
				{
				setState(589);
				breakStatement();
				}
				break;
			case T__49:
				enterOuterAlt(_localctx, 10);
				{
				setState(590);
				returnStatement();
				}
				break;
			case T__50:
				enterOuterAlt(_localctx, 11);
				{
				setState(591);
				throwStatement();
				}
				break;
			case T__51:
				enterOuterAlt(_localctx, 12);
				{
				setState(592);
				emitStatement();
				}
				break;
			case T__43:
				enterOuterAlt(_localctx, 13);
				{
				setState(593);
				placeHolderStatement();
				}
				break;
			case T__3:
			case T__11:
			case T__16:
			case T__23:
			case T__34:
			case T__37:
			case T__52:
			case T__53:
			case T__54:
			case T__55:
			case T__56:
			case T__57:
			case T__58:
			case T__59:
			case T__60:
			case T__81:
			case T__82:
			case T__83:
			case T__84:
			case T__85:
			case T__86:
			case Int:
			case Uint:
			case Byte:
			case Fixed:
			case Ufixed:
			case BooleanLiteral:
			case DecimalNumber:
			case HexNumber:
			case HexLiteral:
			case Identifier:
			case StringLiteral:
			case PLUS:
			case MINUS:
			case NOT:
			case INC:
			case DEC:
				enterOuterAlt(_localctx, 14);
				{
				setState(594);
				simpleStatement();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class PlaceHolderStatementContext extends ParserRuleContext {
		public PlaceHolderStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_placeHolderStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterPlaceHolderStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitPlaceHolderStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitPlaceHolderStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final PlaceHolderStatementContext placeHolderStatement() throws RecognitionException {
		PlaceHolderStatementContext _localctx = new PlaceHolderStatementContext(_ctx, getState());
		enterRule(_localctx, 84, RULE_placeHolderStatement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(597);
			match(T__43);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionStatementContext extends ParserRuleContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public ExpressionStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterExpressionStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitExpressionStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitExpressionStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExpressionStatementContext expressionStatement() throws RecognitionException {
		ExpressionStatementContext _localctx = new ExpressionStatementContext(_ctx, getState());
		enterRule(_localctx, 86, RULE_expressionStatement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(599);
			expression(0);
			setState(600);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class IfStatementContext extends ParserRuleContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public IfStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ifStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterIfStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitIfStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitIfStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final IfStatementContext ifStatement() throws RecognitionException {
		IfStatementContext _localctx = new IfStatementContext(_ctx, getState());
		enterRule(_localctx, 88, RULE_ifStatement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(602);
			match(T__44);
			setState(603);
			match(T__16);
			setState(604);
			expression(0);
			setState(605);
			match(T__17);
			setState(606);
			statement();
			setState(609);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,59,_ctx) ) {
			case 1:
				{
				setState(607);
				match(T__45);
				setState(608);
				statement();
				}
				break;
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class WhileStatementContext extends ParserRuleContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public StatementContext statement() {
			return getRuleContext(StatementContext.class,0);
		}
		public WhileStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_whileStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterWhileStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitWhileStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitWhileStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final WhileStatementContext whileStatement() throws RecognitionException {
		WhileStatementContext _localctx = new WhileStatementContext(_ctx, getState());
		enterRule(_localctx, 90, RULE_whileStatement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(611);
			match(T__46);
			setState(612);
			match(T__16);
			setState(613);
			expression(0);
			setState(614);
			match(T__17);
			setState(615);
			statement();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SimpleStatementContext extends ParserRuleContext {
		public VariableDeclarationStatementContext variableDeclarationStatement() {
			return getRuleContext(VariableDeclarationStatementContext.class,0);
		}
		public ExpressionStatementContext expressionStatement() {
			return getRuleContext(ExpressionStatementContext.class,0);
		}
		public SimpleStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_simpleStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSimpleStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSimpleStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSimpleStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SimpleStatementContext simpleStatement() throws RecognitionException {
		SimpleStatementContext _localctx = new SimpleStatementContext(_ctx, getState());
		enterRule(_localctx, 92, RULE_simpleStatement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(619);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,60,_ctx) ) {
			case 1:
				{
				setState(617);
				variableDeclarationStatement();
				}
				break;
			case 2:
				{
				setState(618);
				expressionStatement();
				}
				break;
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ForStatementContext extends ParserRuleContext {
		public StatementContext statement() {
			return getRuleContext(StatementContext.class,0);
		}
		public SimpleStatementContext simpleStatement() {
			return getRuleContext(SimpleStatementContext.class,0);
		}
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public ForStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_forStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterForStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitForStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitForStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ForStatementContext forStatement() throws RecognitionException {
		ForStatementContext _localctx = new ForStatementContext(_ctx, getState());
		enterRule(_localctx, 94, RULE_forStatement);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(621);
			match(T__19);
			setState(622);
			match(T__16);
			setState(625);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__3:
			case T__11:
			case T__16:
			case T__23:
			case T__34:
			case T__37:
			case T__52:
			case T__53:
			case T__54:
			case T__55:
			case T__56:
			case T__57:
			case T__58:
			case T__59:
			case T__60:
			case T__81:
			case T__82:
			case T__83:
			case T__84:
			case T__85:
			case T__86:
			case Int:
			case Uint:
			case Byte:
			case Fixed:
			case Ufixed:
			case BooleanLiteral:
			case DecimalNumber:
			case HexNumber:
			case HexLiteral:
			case Identifier:
			case StringLiteral:
			case PLUS:
			case MINUS:
			case NOT:
			case INC:
			case DEC:
				{
				setState(623);
				simpleStatement();
				}
				break;
			case T__1:
				{
				setState(624);
				match(T__1);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			setState(628);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__11) | (1L << T__16) | (1L << T__34) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57) | (1L << T__58) | (1L << T__59) | (1L << T__60))) != 0) || ((((_la - 82)) & ~0x3f) == 0 && ((1L << (_la - 82)) & ((1L << (T__81 - 82)) | (1L << (T__82 - 82)) | (1L << (T__83 - 82)) | (1L << (T__84 - 82)) | (1L << (T__85 - 82)) | (1L << (T__86 - 82)) | (1L << (Int - 82)) | (1L << (Uint - 82)) | (1L << (Byte - 82)) | (1L << (Fixed - 82)) | (1L << (Ufixed - 82)) | (1L << (BooleanLiteral - 82)) | (1L << (DecimalNumber - 82)) | (1L << (HexNumber - 82)) | (1L << (HexLiteral - 82)) | (1L << (Identifier - 82)) | (1L << (StringLiteral - 82)) | (1L << (PLUS - 82)) | (1L << (MINUS - 82)) | (1L << (NOT - 82)) | (1L << (INC - 82)) | (1L << (DEC - 82)))) != 0)) {
				{
				setState(627);
				expression(0);
				}
			}

			setState(630);
			match(T__1);
			setState(632);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__11) | (1L << T__16) | (1L << T__34) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57) | (1L << T__58) | (1L << T__59) | (1L << T__60))) != 0) || ((((_la - 82)) & ~0x3f) == 0 && ((1L << (_la - 82)) & ((1L << (T__81 - 82)) | (1L << (T__82 - 82)) | (1L << (T__83 - 82)) | (1L << (T__84 - 82)) | (1L << (T__85 - 82)) | (1L << (T__86 - 82)) | (1L << (Int - 82)) | (1L << (Uint - 82)) | (1L << (Byte - 82)) | (1L << (Fixed - 82)) | (1L << (Ufixed - 82)) | (1L << (BooleanLiteral - 82)) | (1L << (DecimalNumber - 82)) | (1L << (HexNumber - 82)) | (1L << (HexLiteral - 82)) | (1L << (Identifier - 82)) | (1L << (StringLiteral - 82)) | (1L << (PLUS - 82)) | (1L << (MINUS - 82)) | (1L << (NOT - 82)) | (1L << (INC - 82)) | (1L << (DEC - 82)))) != 0)) {
				{
				setState(631);
				expression(0);
				}
			}

			setState(634);
			match(T__17);
			setState(635);
			statement();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class InlineAssemblyStatementContext extends ParserRuleContext {
		public AssemblyBlockContext assemblyBlock() {
			return getRuleContext(AssemblyBlockContext.class,0);
		}
		public TerminalNode StringLiteral() { return getToken(SolidityParser.StringLiteral, 0); }
		public InlineAssemblyStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_inlineAssemblyStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterInlineAssemblyStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitInlineAssemblyStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitInlineAssemblyStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final InlineAssemblyStatementContext inlineAssemblyStatement() throws RecognitionException {
		InlineAssemblyStatementContext _localctx = new InlineAssemblyStatementContext(_ctx, getState());
		enterRule(_localctx, 96, RULE_inlineAssemblyStatement);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(637);
			match(T__47);
			setState(639);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==StringLiteral) {
				{
				setState(638);
				match(StringLiteral);
				}
			}

			setState(641);
			assemblyBlock();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DoWhileStatementContext extends ParserRuleContext {
		public StatementContext statement() {
			return getRuleContext(StatementContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public DoWhileStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_doWhileStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterDoWhileStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitDoWhileStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitDoWhileStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DoWhileStatementContext doWhileStatement() throws RecognitionException {
		DoWhileStatementContext _localctx = new DoWhileStatementContext(_ctx, getState());
		enterRule(_localctx, 98, RULE_doWhileStatement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(643);
			match(T__48);
			setState(644);
			statement();
			setState(645);
			match(T__46);
			setState(646);
			match(T__16);
			setState(647);
			expression(0);
			setState(648);
			match(T__17);
			setState(649);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ContinueStatementContext extends ParserRuleContext {
		public TerminalNode ContinueKeyword() { return getToken(SolidityParser.ContinueKeyword, 0); }
		public ContinueStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_continueStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterContinueStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitContinueStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitContinueStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ContinueStatementContext continueStatement() throws RecognitionException {
		ContinueStatementContext _localctx = new ContinueStatementContext(_ctx, getState());
		enterRule(_localctx, 100, RULE_continueStatement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(651);
			match(ContinueKeyword);
			setState(652);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class BreakStatementContext extends ParserRuleContext {
		public TerminalNode BreakKeyword() { return getToken(SolidityParser.BreakKeyword, 0); }
		public BreakStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_breakStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterBreakStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitBreakStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitBreakStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BreakStatementContext breakStatement() throws RecognitionException {
		BreakStatementContext _localctx = new BreakStatementContext(_ctx, getState());
		enterRule(_localctx, 102, RULE_breakStatement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(654);
			match(BreakKeyword);
			setState(655);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ReturnStatementContext extends ParserRuleContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public ReturnStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_returnStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterReturnStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitReturnStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitReturnStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ReturnStatementContext returnStatement() throws RecognitionException {
		ReturnStatementContext _localctx = new ReturnStatementContext(_ctx, getState());
		enterRule(_localctx, 104, RULE_returnStatement);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(657);
			match(T__49);
			setState(659);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__11) | (1L << T__16) | (1L << T__34) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57) | (1L << T__58) | (1L << T__59) | (1L << T__60))) != 0) || ((((_la - 82)) & ~0x3f) == 0 && ((1L << (_la - 82)) & ((1L << (T__81 - 82)) | (1L << (T__82 - 82)) | (1L << (T__83 - 82)) | (1L << (T__84 - 82)) | (1L << (T__85 - 82)) | (1L << (T__86 - 82)) | (1L << (Int - 82)) | (1L << (Uint - 82)) | (1L << (Byte - 82)) | (1L << (Fixed - 82)) | (1L << (Ufixed - 82)) | (1L << (BooleanLiteral - 82)) | (1L << (DecimalNumber - 82)) | (1L << (HexNumber - 82)) | (1L << (HexLiteral - 82)) | (1L << (Identifier - 82)) | (1L << (StringLiteral - 82)) | (1L << (PLUS - 82)) | (1L << (MINUS - 82)) | (1L << (NOT - 82)) | (1L << (INC - 82)) | (1L << (DEC - 82)))) != 0)) {
				{
				setState(658);
				expression(0);
				}
			}

			setState(661);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ThrowStatementContext extends ParserRuleContext {
		public ThrowStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_throwStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterThrowStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitThrowStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitThrowStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ThrowStatementContext throwStatement() throws RecognitionException {
		ThrowStatementContext _localctx = new ThrowStatementContext(_ctx, getState());
		enterRule(_localctx, 106, RULE_throwStatement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(663);
			match(T__50);
			setState(664);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class EmitStatementContext extends ParserRuleContext {
		public FunctionCallContext functionCall() {
			return getRuleContext(FunctionCallContext.class,0);
		}
		public EmitStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_emitStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterEmitStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitEmitStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitEmitStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final EmitStatementContext emitStatement() throws RecognitionException {
		EmitStatementContext _localctx = new EmitStatementContext(_ctx, getState());
		enterRule(_localctx, 108, RULE_emitStatement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(666);
			match(T__51);
			setState(667);
			functionCall();
			setState(668);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VariableDeclarationStatementContext extends ParserRuleContext {
		public IdentifierListContext identifierList() {
			return getRuleContext(IdentifierListContext.class,0);
		}
		public VariableDeclarationContext variableDeclaration() {
			return getRuleContext(VariableDeclarationContext.class,0);
		}
		public VariableDeclarationListContext variableDeclarationList() {
			return getRuleContext(VariableDeclarationListContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public VariableDeclarationStatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_variableDeclarationStatement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterVariableDeclarationStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitVariableDeclarationStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitVariableDeclarationStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VariableDeclarationStatementContext variableDeclarationStatement() throws RecognitionException {
		VariableDeclarationStatementContext _localctx = new VariableDeclarationStatementContext(_ctx, getState());
		enterRule(_localctx, 110, RULE_variableDeclarationStatement);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(677);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,66,_ctx) ) {
			case 1:
				{
				setState(670);
				match(T__52);
				setState(671);
				identifierList();
				}
				break;
			case 2:
				{
				setState(672);
				variableDeclaration();
				}
				break;
			case 3:
				{
				setState(673);
				match(T__16);
				setState(674);
				variableDeclarationList();
				setState(675);
				match(T__17);
				}
				break;
			}
			setState(681);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__8) {
				{
				setState(679);
				match(T__8);
				setState(680);
				expression(0);
				}
			}

			setState(683);
			match(T__1);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VariableDeclarationListContext extends ParserRuleContext {
		public List<VariableDeclarationContext> variableDeclaration() {
			return getRuleContexts(VariableDeclarationContext.class);
		}
		public VariableDeclarationContext variableDeclaration(int i) {
			return getRuleContext(VariableDeclarationContext.class,i);
		}
		public VariableDeclarationListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_variableDeclarationList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterVariableDeclarationList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitVariableDeclarationList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitVariableDeclarationList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VariableDeclarationListContext variableDeclarationList() throws RecognitionException {
		VariableDeclarationListContext _localctx = new VariableDeclarationListContext(_ctx, getState());
		enterRule(_localctx, 112, RULE_variableDeclarationList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(686);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__23) | (1L << T__37) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57))) != 0) || ((((_la - 96)) & ~0x3f) == 0 && ((1L << (_la - 96)) & ((1L << (Int - 96)) | (1L << (Uint - 96)) | (1L << (Byte - 96)) | (1L << (Fixed - 96)) | (1L << (Ufixed - 96)) | (1L << (Identifier - 96)))) != 0)) {
				{
				setState(685);
				variableDeclaration();
				}
			}

			setState(694);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__13) {
				{
				{
				setState(688);
				match(T__13);
				setState(690);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__23) | (1L << T__37) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57))) != 0) || ((((_la - 96)) & ~0x3f) == 0 && ((1L << (_la - 96)) & ((1L << (Int - 96)) | (1L << (Uint - 96)) | (1L << (Byte - 96)) | (1L << (Fixed - 96)) | (1L << (Ufixed - 96)) | (1L << (Identifier - 96)))) != 0)) {
					{
					setState(689);
					variableDeclaration();
					}
				}

				}
				}
				setState(696);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class IdentifierListContext extends ParserRuleContext {
		public List<IdentifierContext> identifier() {
			return getRuleContexts(IdentifierContext.class);
		}
		public IdentifierContext identifier(int i) {
			return getRuleContext(IdentifierContext.class,i);
		}
		public IdentifierListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_identifierList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterIdentifierList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitIdentifierList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitIdentifierList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final IdentifierListContext identifierList() throws RecognitionException {
		IdentifierListContext _localctx = new IdentifierListContext(_ctx, getState());
		enterRule(_localctx, 114, RULE_identifierList);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(697);
			match(T__16);
			setState(704);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,72,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(699);
					_errHandler.sync(this);
					_la = _input.LA(1);
					if (_la==T__11 || _la==Identifier) {
						{
						setState(698);
						identifier();
						}
					}

					setState(701);
					match(T__13);
					}
					} 
				}
				setState(706);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,72,_ctx);
			}
			setState(708);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__11 || _la==Identifier) {
				{
				setState(707);
				identifier();
				}
			}

			setState(710);
			match(T__17);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ElementaryTypeNameContext extends ParserRuleContext {
		public TerminalNode Int() { return getToken(SolidityParser.Int, 0); }
		public TerminalNode Uint() { return getToken(SolidityParser.Uint, 0); }
		public TerminalNode Byte() { return getToken(SolidityParser.Byte, 0); }
		public TerminalNode Fixed() { return getToken(SolidityParser.Fixed, 0); }
		public TerminalNode Ufixed() { return getToken(SolidityParser.Ufixed, 0); }
		public ElementaryTypeNameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_elementaryTypeName; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterElementaryTypeName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitElementaryTypeName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitElementaryTypeName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ElementaryTypeNameContext elementaryTypeName() throws RecognitionException {
		ElementaryTypeNameContext _localctx = new ElementaryTypeNameContext(_ctx, getState());
		enterRule(_localctx, 116, RULE_elementaryTypeName);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(712);
			_la = _input.LA(1);
			if ( !(((((_la - 53)) & ~0x3f) == 0 && ((1L << (_la - 53)) & ((1L << (T__52 - 53)) | (1L << (T__53 - 53)) | (1L << (T__54 - 53)) | (1L << (T__55 - 53)) | (1L << (T__56 - 53)) | (1L << (T__57 - 53)) | (1L << (Int - 53)) | (1L << (Uint - 53)) | (1L << (Byte - 53)) | (1L << (Fixed - 53)) | (1L << (Ufixed - 53)))) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionContext extends ParserRuleContext {
		public ExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expression; }
	 
		public ExpressionContext() { }
		public void copyFrom(ExpressionContext ctx) {
			super.copyFrom(ctx);
		}
	}
	public static class EquivalenceExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public EquivalenceExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterEquivalenceExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitEquivalenceExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitEquivalenceExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class NetExpressionContext extends ExpressionContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public NetExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterNetExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitNetExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitNetExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AdditiveExpressionContext extends ExpressionContext {
		public Token binop;
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TerminalNode PLUS() { return getToken(SolidityParser.PLUS, 0); }
		public TerminalNode MINUS() { return getToken(SolidityParser.MINUS, 0); }
		public AdditiveExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAdditiveExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAdditiveExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAdditiveExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class TildeExpressionContext extends ExpressionContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public TildeExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterTildeExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitTildeExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitTildeExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class NotExpressionContext extends ExpressionContext {
		public TerminalNode NOT() { return getToken(SolidityParser.NOT, 0); }
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public NotExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterNotExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitNotExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitNotExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ParenExpressionContext extends ExpressionContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public ParenExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterParenExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitParenExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitParenExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class PreIncOrDecExpressionContext extends ExpressionContext {
		public Token unop;
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public TerminalNode INC() { return getToken(SolidityParser.INC, 0); }
		public TerminalNode DEC() { return getToken(SolidityParser.DEC, 0); }
		public PreIncOrDecExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterPreIncOrDecExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitPreIncOrDecExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitPreIncOrDecExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class LogicalShiftExpressionContext extends ExpressionContext {
		public Token binop;
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TerminalNode LSL() { return getToken(SolidityParser.LSL, 0); }
		public TerminalNode LSR() { return getToken(SolidityParser.LSR, 0); }
		public LogicalShiftExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterLogicalShiftExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitLogicalShiftExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitLogicalShiftExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class PostIncOrDecExpressionContext extends ExpressionContext {
		public Token unop;
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public TerminalNode INC() { return getToken(SolidityParser.INC, 0); }
		public TerminalNode DEC() { return getToken(SolidityParser.DEC, 0); }
		public PostIncOrDecExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterPostIncOrDecExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitPostIncOrDecExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitPostIncOrDecExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AndExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TerminalNode AND() { return getToken(SolidityParser.AND, 0); }
		public AndExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAndExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAndExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAndExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class CompExpressionContext extends ExpressionContext {
		public Token binop;
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public CompExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterCompExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitCompExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitCompExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ForallExpressionContext extends ExpressionContext {
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public TerminalNode Identifier() { return getToken(SolidityParser.Identifier, 0); }
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public ForallExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterForallExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitForallExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitForallExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ExistsExpressionContext extends ExpressionContext {
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public TerminalNode Identifier() { return getToken(SolidityParser.Identifier, 0); }
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public ExistsExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterExistsExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitExistsExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitExistsExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class BitwiseAndExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TerminalNode BAND() { return getToken(SolidityParser.BAND, 0); }
		public BitwiseAndExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterBitwiseAndExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitBitwiseAndExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitBitwiseAndExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class FunctionCallExpressionContext extends ExpressionContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public FunctionCallArgumentsContext functionCallArguments() {
			return getRuleContext(FunctionCallArgumentsContext.class,0);
		}
		public FunctionCallExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterFunctionCallExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitFunctionCallExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitFunctionCallExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class MinMaxTypeExprExpressionContext extends ExpressionContext {
		public MinMaxTypeExpressionContext minMaxTypeExpression() {
			return getRuleContext(MinMaxTypeExpressionContext.class,0);
		}
		public MinMaxTypeExprExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterMinMaxTypeExprExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitMinMaxTypeExprExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitMinMaxTypeExprExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class PrimaryExprExpressionContext extends ExpressionContext {
		public PrimaryExpressionContext primaryExpression() {
			return getRuleContext(PrimaryExpressionContext.class,0);
		}
		public PrimaryExprExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterPrimaryExprExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitPrimaryExprExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitPrimaryExprExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class BitwiseXorExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public BitwiseXorExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterBitwiseXorExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitBitwiseXorExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitBitwiseXorExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class DotExpressionContext extends ExpressionContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public DotExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterDotExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitDotExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitDotExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class UnaryAdditiveExpressionContext extends ExpressionContext {
		public Token unop;
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public TerminalNode PLUS() { return getToken(SolidityParser.PLUS, 0); }
		public TerminalNode MINUS() { return getToken(SolidityParser.MINUS, 0); }
		public UnaryAdditiveExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterUnaryAdditiveExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitUnaryAdditiveExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitUnaryAdditiveExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class NewTypeNameExpressionContext extends ExpressionContext {
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public NewTypeNameExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterNewTypeNameExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitNewTypeNameExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitNewTypeNameExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class AssignmentExpressionContext extends ExpressionContext {
		public Token binop;
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public AssignmentExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssignmentExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssignmentExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssignmentExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class MultiplicativeExpressionContext extends ExpressionContext {
		public Token binop;
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TerminalNode MULT() { return getToken(SolidityParser.MULT, 0); }
		public TerminalNode DIV() { return getToken(SolidityParser.DIV, 0); }
		public TerminalNode MOD() { return getToken(SolidityParser.MOD, 0); }
		public MultiplicativeExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterMultiplicativeExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitMultiplicativeExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitMultiplicativeExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class OrExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TerminalNode OR() { return getToken(SolidityParser.OR, 0); }
		public OrExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterOrExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitOrExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitOrExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class PowerExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public PowerExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterPowerExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitPowerExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitPowerExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class GrossFromExpressionContext extends ExpressionContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public GrossFromExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterGrossFromExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitGrossFromExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitGrossFromExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class BitwiseOrExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TerminalNode BOR() { return getToken(SolidityParser.BOR, 0); }
		public BitwiseOrExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterBitwiseOrExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitBitwiseOrExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitBitwiseOrExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ArrayAccessExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public ArrayAccessExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterArrayAccessExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitArrayAccessExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitArrayAccessExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class DeleteExpressionContext extends ExpressionContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public DeleteExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterDeleteExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitDeleteExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitDeleteExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class EqualityExpressionContext extends ExpressionContext {
		public Token binop;
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public EqualityExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterEqualityExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitEqualityExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitEqualityExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class GrossToExpressionContext extends ExpressionContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public GrossToExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterGrossToExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitGrossToExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitGrossToExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ImplicationExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public ImplicationExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterImplicationExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitImplicationExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitImplicationExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class OldExpressionContext extends ExpressionContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public OldExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterOldExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitOldExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitOldExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class OnlyIfExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public OnlyIfExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterOnlyIfExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitOnlyIfExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitOnlyIfExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class ResultExpressionContext extends ExpressionContext {
		public ResultExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterResultExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitResultExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitResultExpression(this);
			else return visitor.visitChildren(this);
		}
	}
	public static class TernaryExpressionContext extends ExpressionContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TernaryExpressionContext(ExpressionContext ctx) { copyFrom(ctx); }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterTernaryExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitTernaryExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitTernaryExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExpressionContext expression() throws RecognitionException {
		return expression(0);
	}

	private ExpressionContext expression(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ExpressionContext _localctx = new ExpressionContext(_ctx, _parentState);
		ExpressionContext _prevctx = _localctx;
		int _startState = 118;
		enterRecursionRule(_localctx, 118, RULE_expression, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(770);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,74,_ctx) ) {
			case 1:
				{
				_localctx = new NewTypeNameExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;

				setState(715);
				match(T__58);
				setState(716);
				typeName(0);
				}
				break;
			case 2:
				{
				_localctx = new ParenExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(717);
				match(T__16);
				setState(718);
				expression(0);
				setState(719);
				match(T__17);
				}
				break;
			case 3:
				{
				_localctx = new PreIncOrDecExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(721);
				((PreIncOrDecExpressionContext)_localctx).unop = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==INC || _la==DEC) ) {
					((PreIncOrDecExpressionContext)_localctx).unop = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(722);
				expression(30);
				}
				break;
			case 4:
				{
				_localctx = new UnaryAdditiveExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(723);
				((UnaryAdditiveExpressionContext)_localctx).unop = _input.LT(1);
				_la = _input.LA(1);
				if ( !(_la==PLUS || _la==MINUS) ) {
					((UnaryAdditiveExpressionContext)_localctx).unop = (Token)_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(724);
				expression(29);
				}
				break;
			case 5:
				{
				_localctx = new DeleteExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(725);
				_la = _input.LA(1);
				if ( !(_la==T__59 || _la==T__60) ) {
				_errHandler.recoverInline(this);
				}
				else {
					if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
					_errHandler.reportMatch(this);
					consume();
				}
				setState(726);
				expression(28);
				}
				break;
			case 6:
				{
				_localctx = new NotExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(727);
				match(NOT);
				setState(728);
				expression(27);
				}
				break;
			case 7:
				{
				_localctx = new TildeExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(729);
				match(T__3);
				setState(730);
				expression(26);
				}
				break;
			case 8:
				{
				_localctx = new PrimaryExprExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(731);
				primaryExpression();
				}
				break;
			case 9:
				{
				_localctx = new MinMaxTypeExprExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(732);
				minMaxTypeExpression();
				}
				break;
			case 10:
				{
				_localctx = new ForallExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(733);
				match(T__16);
				setState(734);
				match(T__79);
				setState(735);
				typeName(0);
				setState(736);
				match(Identifier);
				setState(737);
				match(T__1);
				setState(738);
				expression(0);
				setState(739);
				match(T__17);
				}
				break;
			case 11:
				{
				_localctx = new ExistsExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(741);
				match(T__16);
				setState(742);
				match(T__80);
				setState(743);
				typeName(0);
				setState(744);
				match(Identifier);
				setState(745);
				match(T__1);
				setState(746);
				expression(0);
				setState(747);
				match(T__17);
				}
				break;
			case 12:
				{
				_localctx = new NetExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(749);
				match(T__81);
				setState(750);
				match(T__16);
				setState(751);
				expression(0);
				setState(752);
				match(T__17);
				}
				break;
			case 13:
				{
				_localctx = new GrossFromExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(754);
				match(T__82);
				setState(755);
				match(T__16);
				setState(756);
				expression(0);
				setState(757);
				match(T__17);
				}
				break;
			case 14:
				{
				_localctx = new GrossToExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(759);
				match(T__83);
				setState(760);
				match(T__16);
				setState(761);
				expression(0);
				setState(762);
				match(T__17);
				}
				break;
			case 15:
				{
				_localctx = new OldExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(764);
				match(T__84);
				setState(765);
				match(T__16);
				setState(766);
				expression(0);
				setState(767);
				match(T__17);
				}
				break;
			case 16:
				{
				_localctx = new ResultExpressionContext(_localctx);
				_ctx = _localctx;
				_prevctx = _localctx;
				setState(769);
				match(T__85);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(840);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,76,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(838);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,75,_ctx) ) {
					case 1:
						{
						_localctx = new PowerExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(772);
						if (!(precpred(_ctx, 25))) throw new FailedPredicateException(this, "precpred(_ctx, 25)");
						setState(773);
						match(T__61);
						setState(774);
						expression(26);
						}
						break;
					case 2:
						{
						_localctx = new MultiplicativeExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(775);
						if (!(precpred(_ctx, 24))) throw new FailedPredicateException(this, "precpred(_ctx, 24)");
						setState(776);
						((MultiplicativeExpressionContext)_localctx).binop = _input.LT(1);
						_la = _input.LA(1);
						if ( !(((((_la - 131)) & ~0x3f) == 0 && ((1L << (_la - 131)) & ((1L << (MULT - 131)) | (1L << (DIV - 131)) | (1L << (MOD - 131)))) != 0)) ) {
							((MultiplicativeExpressionContext)_localctx).binop = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(777);
						expression(25);
						}
						break;
					case 3:
						{
						_localctx = new AdditiveExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(778);
						if (!(precpred(_ctx, 23))) throw new FailedPredicateException(this, "precpred(_ctx, 23)");
						setState(779);
						((AdditiveExpressionContext)_localctx).binop = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==PLUS || _la==MINUS) ) {
							((AdditiveExpressionContext)_localctx).binop = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(780);
						expression(24);
						}
						break;
					case 4:
						{
						_localctx = new LogicalShiftExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(781);
						if (!(precpred(_ctx, 22))) throw new FailedPredicateException(this, "precpred(_ctx, 22)");
						setState(782);
						((LogicalShiftExpressionContext)_localctx).binop = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==LSL || _la==LSR) ) {
							((LogicalShiftExpressionContext)_localctx).binop = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(783);
						expression(23);
						}
						break;
					case 5:
						{
						_localctx = new BitwiseAndExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(784);
						if (!(precpred(_ctx, 21))) throw new FailedPredicateException(this, "precpred(_ctx, 21)");
						setState(785);
						match(BAND);
						setState(786);
						expression(22);
						}
						break;
					case 6:
						{
						_localctx = new BitwiseXorExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(787);
						if (!(precpred(_ctx, 20))) throw new FailedPredicateException(this, "precpred(_ctx, 20)");
						setState(788);
						match(T__2);
						setState(789);
						expression(21);
						}
						break;
					case 7:
						{
						_localctx = new BitwiseOrExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(790);
						if (!(precpred(_ctx, 19))) throw new FailedPredicateException(this, "precpred(_ctx, 19)");
						setState(791);
						match(BOR);
						setState(792);
						expression(20);
						}
						break;
					case 8:
						{
						_localctx = new CompExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(793);
						if (!(precpred(_ctx, 18))) throw new FailedPredicateException(this, "precpred(_ctx, 18)");
						setState(794);
						((CompExpressionContext)_localctx).binop = _input.LT(1);
						_la = _input.LA(1);
						if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__4) | (1L << T__5) | (1L << T__6) | (1L << T__7))) != 0)) ) {
							((CompExpressionContext)_localctx).binop = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(795);
						expression(19);
						}
						break;
					case 9:
						{
						_localctx = new EqualityExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(796);
						if (!(precpred(_ctx, 17))) throw new FailedPredicateException(this, "precpred(_ctx, 17)");
						setState(797);
						((EqualityExpressionContext)_localctx).binop = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__62 || _la==T__63) ) {
							((EqualityExpressionContext)_localctx).binop = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(798);
						expression(18);
						}
						break;
					case 10:
						{
						_localctx = new AndExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(799);
						if (!(precpred(_ctx, 16))) throw new FailedPredicateException(this, "precpred(_ctx, 16)");
						setState(800);
						match(AND);
						setState(801);
						expression(17);
						}
						break;
					case 11:
						{
						_localctx = new OrExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(802);
						if (!(precpred(_ctx, 15))) throw new FailedPredicateException(this, "precpred(_ctx, 15)");
						setState(803);
						match(OR);
						setState(804);
						expression(16);
						}
						break;
					case 12:
						{
						_localctx = new TernaryExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(805);
						if (!(precpred(_ctx, 14))) throw new FailedPredicateException(this, "precpred(_ctx, 14)");
						setState(806);
						match(T__64);
						setState(807);
						expression(0);
						setState(808);
						match(T__65);
						setState(809);
						expression(15);
						}
						break;
					case 13:
						{
						_localctx = new AssignmentExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(811);
						if (!(precpred(_ctx, 13))) throw new FailedPredicateException(this, "precpred(_ctx, 13)");
						setState(812);
						((AssignmentExpressionContext)_localctx).binop = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==T__8 || ((((_la - 67)) & ~0x3f) == 0 && ((1L << (_la - 67)) & ((1L << (T__66 - 67)) | (1L << (T__67 - 67)) | (1L << (T__68 - 67)) | (1L << (T__69 - 67)) | (1L << (T__70 - 67)) | (1L << (T__71 - 67)) | (1L << (T__72 - 67)) | (1L << (T__73 - 67)) | (1L << (T__74 - 67)) | (1L << (T__75 - 67)))) != 0)) ) {
							((AssignmentExpressionContext)_localctx).binop = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						setState(813);
						expression(14);
						}
						break;
					case 14:
						{
						_localctx = new ImplicationExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(814);
						if (!(precpred(_ctx, 11))) throw new FailedPredicateException(this, "precpred(_ctx, 11)");
						setState(815);
						match(T__76);
						setState(816);
						expression(12);
						}
						break;
					case 15:
						{
						_localctx = new EquivalenceExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(817);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(818);
						match(T__77);
						setState(819);
						expression(11);
						}
						break;
					case 16:
						{
						_localctx = new OnlyIfExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(820);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(821);
						match(T__78);
						setState(822);
						expression(10);
						}
						break;
					case 17:
						{
						_localctx = new PostIncOrDecExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(823);
						if (!(precpred(_ctx, 36))) throw new FailedPredicateException(this, "precpred(_ctx, 36)");
						setState(824);
						((PostIncOrDecExpressionContext)_localctx).unop = _input.LT(1);
						_la = _input.LA(1);
						if ( !(_la==INC || _la==DEC) ) {
							((PostIncOrDecExpressionContext)_localctx).unop = (Token)_errHandler.recoverInline(this);
						}
						else {
							if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
							_errHandler.reportMatch(this);
							consume();
						}
						}
						break;
					case 18:
						{
						_localctx = new ArrayAccessExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(825);
						if (!(precpred(_ctx, 34))) throw new FailedPredicateException(this, "precpred(_ctx, 34)");
						setState(826);
						match(T__34);
						setState(827);
						expression(0);
						setState(828);
						match(T__35);
						}
						break;
					case 19:
						{
						_localctx = new FunctionCallExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(830);
						if (!(precpred(_ctx, 33))) throw new FailedPredicateException(this, "precpred(_ctx, 33)");
						setState(831);
						match(T__16);
						setState(832);
						functionCallArguments();
						setState(833);
						match(T__17);
						}
						break;
					case 20:
						{
						_localctx = new DotExpressionContext(new ExpressionContext(_parentctx, _parentState));
						pushNewRecursionContext(_localctx, _startState, RULE_expression);
						setState(835);
						if (!(precpred(_ctx, 32))) throw new FailedPredicateException(this, "precpred(_ctx, 32)");
						setState(836);
						match(T__36);
						setState(837);
						identifier();
						}
						break;
					}
					} 
				}
				setState(842);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,76,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class PrimaryExpressionContext extends ParserRuleContext {
		public TerminalNode BooleanLiteral() { return getToken(SolidityParser.BooleanLiteral, 0); }
		public NumberLiteralContext numberLiteral() {
			return getRuleContext(NumberLiteralContext.class,0);
		}
		public TerminalNode HexLiteral() { return getToken(SolidityParser.HexLiteral, 0); }
		public TerminalNode StringLiteral() { return getToken(SolidityParser.StringLiteral, 0); }
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public TupleExpressionContext tupleExpression() {
			return getRuleContext(TupleExpressionContext.class,0);
		}
		public ElementaryTypeNameExpressionContext elementaryTypeNameExpression() {
			return getRuleContext(ElementaryTypeNameExpressionContext.class,0);
		}
		public PrimaryExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_primaryExpression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterPrimaryExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitPrimaryExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitPrimaryExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final PrimaryExpressionContext primaryExpression() throws RecognitionException {
		PrimaryExpressionContext _localctx = new PrimaryExpressionContext(_ctx, getState());
		enterRule(_localctx, 120, RULE_primaryExpression);
		try {
			setState(850);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case BooleanLiteral:
				enterOuterAlt(_localctx, 1);
				{
				setState(843);
				match(BooleanLiteral);
				}
				break;
			case DecimalNumber:
			case HexNumber:
				enterOuterAlt(_localctx, 2);
				{
				setState(844);
				numberLiteral();
				}
				break;
			case HexLiteral:
				enterOuterAlt(_localctx, 3);
				{
				setState(845);
				match(HexLiteral);
				}
				break;
			case StringLiteral:
				enterOuterAlt(_localctx, 4);
				{
				setState(846);
				match(StringLiteral);
				}
				break;
			case T__11:
			case Identifier:
				enterOuterAlt(_localctx, 5);
				{
				setState(847);
				identifier();
				}
				break;
			case T__16:
			case T__34:
				enterOuterAlt(_localctx, 6);
				{
				setState(848);
				tupleExpression();
				}
				break;
			case T__52:
			case T__53:
			case T__54:
			case T__55:
			case T__56:
			case T__57:
			case Int:
			case Uint:
			case Byte:
			case Fixed:
			case Ufixed:
				enterOuterAlt(_localctx, 7);
				{
				setState(849);
				elementaryTypeNameExpression();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MinMaxTypeExpressionContext extends ParserRuleContext {
		public TypeNameContext typeName() {
			return getRuleContext(TypeNameContext.class,0);
		}
		public MinMaxTypeExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_minMaxTypeExpression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterMinMaxTypeExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitMinMaxTypeExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitMinMaxTypeExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final MinMaxTypeExpressionContext minMaxTypeExpression() throws RecognitionException {
		MinMaxTypeExpressionContext _localctx = new MinMaxTypeExpressionContext(_ctx, getState());
		enterRule(_localctx, 122, RULE_minMaxTypeExpression);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(852);
			match(T__86);
			setState(853);
			match(T__16);
			setState(854);
			typeName(0);
			setState(855);
			match(T__17);
			setState(856);
			match(T__36);
			setState(857);
			_la = _input.LA(1);
			if ( !(_la==T__87 || _la==T__88) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ExpressionListContext extends ParserRuleContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public ExpressionListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expressionList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterExpressionList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitExpressionList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitExpressionList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExpressionListContext expressionList() throws RecognitionException {
		ExpressionListContext _localctx = new ExpressionListContext(_ctx, getState());
		enterRule(_localctx, 124, RULE_expressionList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(859);
			expression(0);
			setState(864);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__13) {
				{
				{
				setState(860);
				match(T__13);
				setState(861);
				expression(0);
				}
				}
				setState(866);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class NameValueListContext extends ParserRuleContext {
		public List<NameValueContext> nameValue() {
			return getRuleContexts(NameValueContext.class);
		}
		public NameValueContext nameValue(int i) {
			return getRuleContext(NameValueContext.class,i);
		}
		public NameValueListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_nameValueList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterNameValueList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitNameValueList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitNameValueList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final NameValueListContext nameValueList() throws RecognitionException {
		NameValueListContext _localctx = new NameValueListContext(_ctx, getState());
		enterRule(_localctx, 126, RULE_nameValueList);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(867);
			nameValue();
			setState(872);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,79,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(868);
					match(T__13);
					setState(869);
					nameValue();
					}
					} 
				}
				setState(874);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,79,_ctx);
			}
			setState(876);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__13) {
				{
				setState(875);
				match(T__13);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class NameValueContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public NameValueContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_nameValue; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterNameValue(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitNameValue(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitNameValue(this);
			else return visitor.visitChildren(this);
		}
	}

	public final NameValueContext nameValue() throws RecognitionException {
		NameValueContext _localctx = new NameValueContext(_ctx, getState());
		enterRule(_localctx, 128, RULE_nameValue);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(878);
			identifier();
			setState(879);
			match(T__65);
			setState(880);
			expression(0);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FunctionCallArgumentsContext extends ParserRuleContext {
		public NameValueListContext nameValueList() {
			return getRuleContext(NameValueListContext.class,0);
		}
		public ExpressionListContext expressionList() {
			return getRuleContext(ExpressionListContext.class,0);
		}
		public FunctionCallArgumentsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_functionCallArguments; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterFunctionCallArguments(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitFunctionCallArguments(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitFunctionCallArguments(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FunctionCallArgumentsContext functionCallArguments() throws RecognitionException {
		FunctionCallArgumentsContext _localctx = new FunctionCallArgumentsContext(_ctx, getState());
		enterRule(_localctx, 130, RULE_functionCallArguments);
		int _la;
		try {
			setState(890);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__12:
				enterOuterAlt(_localctx, 1);
				{
				setState(882);
				match(T__12);
				setState(884);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__11 || _la==Identifier) {
					{
					setState(883);
					nameValueList();
					}
				}

				setState(886);
				match(T__14);
				}
				break;
			case T__3:
			case T__11:
			case T__16:
			case T__17:
			case T__34:
			case T__52:
			case T__53:
			case T__54:
			case T__55:
			case T__56:
			case T__57:
			case T__58:
			case T__59:
			case T__60:
			case T__81:
			case T__82:
			case T__83:
			case T__84:
			case T__85:
			case T__86:
			case Int:
			case Uint:
			case Byte:
			case Fixed:
			case Ufixed:
			case BooleanLiteral:
			case DecimalNumber:
			case HexNumber:
			case HexLiteral:
			case Identifier:
			case StringLiteral:
			case PLUS:
			case MINUS:
			case NOT:
			case INC:
			case DEC:
				enterOuterAlt(_localctx, 2);
				{
				setState(888);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__11) | (1L << T__16) | (1L << T__34) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57) | (1L << T__58) | (1L << T__59) | (1L << T__60))) != 0) || ((((_la - 82)) & ~0x3f) == 0 && ((1L << (_la - 82)) & ((1L << (T__81 - 82)) | (1L << (T__82 - 82)) | (1L << (T__83 - 82)) | (1L << (T__84 - 82)) | (1L << (T__85 - 82)) | (1L << (T__86 - 82)) | (1L << (Int - 82)) | (1L << (Uint - 82)) | (1L << (Byte - 82)) | (1L << (Fixed - 82)) | (1L << (Ufixed - 82)) | (1L << (BooleanLiteral - 82)) | (1L << (DecimalNumber - 82)) | (1L << (HexNumber - 82)) | (1L << (HexLiteral - 82)) | (1L << (Identifier - 82)) | (1L << (StringLiteral - 82)) | (1L << (PLUS - 82)) | (1L << (MINUS - 82)) | (1L << (NOT - 82)) | (1L << (INC - 82)) | (1L << (DEC - 82)))) != 0)) {
					{
					setState(887);
					expressionList();
					}
				}

				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class FunctionCallContext extends ParserRuleContext {
		public ExpressionContext expression() {
			return getRuleContext(ExpressionContext.class,0);
		}
		public FunctionCallArgumentsContext functionCallArguments() {
			return getRuleContext(FunctionCallArgumentsContext.class,0);
		}
		public FunctionCallContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_functionCall; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterFunctionCall(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitFunctionCall(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitFunctionCall(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FunctionCallContext functionCall() throws RecognitionException {
		FunctionCallContext _localctx = new FunctionCallContext(_ctx, getState());
		enterRule(_localctx, 132, RULE_functionCall);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(892);
			expression(0);
			setState(893);
			match(T__16);
			setState(894);
			functionCallArguments();
			setState(895);
			match(T__17);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyBlockContext extends ParserRuleContext {
		public List<AssemblyItemContext> assemblyItem() {
			return getRuleContexts(AssemblyItemContext.class);
		}
		public AssemblyItemContext assemblyItem(int i) {
			return getRuleContext(AssemblyItemContext.class,i);
		}
		public AssemblyBlockContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyBlock; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyBlock(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyBlock(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyBlock(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyBlockContext assemblyBlock() throws RecognitionException {
		AssemblyBlockContext _localctx = new AssemblyBlockContext(_ctx, getState());
		enterRule(_localctx, 134, RULE_assemblyBlock);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(897);
			match(T__12);
			setState(901);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__12) | (1L << T__16) | (1L << T__19) | (1L << T__23) | (1L << T__44) | (1L << T__47) | (1L << T__49) | (1L << T__53) | (1L << T__57))) != 0) || ((((_la - 90)) & ~0x3f) == 0 && ((1L << (_la - 90)) & ((1L << (T__89 - 90)) | (1L << (T__91 - 90)) | (1L << (T__92 - 90)) | (1L << (DecimalNumber - 90)) | (1L << (HexNumber - 90)) | (1L << (HexLiteral - 90)) | (1L << (BreakKeyword - 90)) | (1L << (ContinueKeyword - 90)) | (1L << (Identifier - 90)) | (1L << (StringLiteral - 90)))) != 0)) {
				{
				{
				setState(898);
				assemblyItem();
				}
				}
				setState(903);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(904);
			match(T__14);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyItemContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public AssemblyBlockContext assemblyBlock() {
			return getRuleContext(AssemblyBlockContext.class,0);
		}
		public AssemblyExpressionContext assemblyExpression() {
			return getRuleContext(AssemblyExpressionContext.class,0);
		}
		public AssemblyLocalDefinitionContext assemblyLocalDefinition() {
			return getRuleContext(AssemblyLocalDefinitionContext.class,0);
		}
		public AssemblyAssignmentContext assemblyAssignment() {
			return getRuleContext(AssemblyAssignmentContext.class,0);
		}
		public AssemblyStackAssignmentContext assemblyStackAssignment() {
			return getRuleContext(AssemblyStackAssignmentContext.class,0);
		}
		public LabelDefinitionContext labelDefinition() {
			return getRuleContext(LabelDefinitionContext.class,0);
		}
		public AssemblySwitchContext assemblySwitch() {
			return getRuleContext(AssemblySwitchContext.class,0);
		}
		public AssemblyFunctionDefinitionContext assemblyFunctionDefinition() {
			return getRuleContext(AssemblyFunctionDefinitionContext.class,0);
		}
		public AssemblyForContext assemblyFor() {
			return getRuleContext(AssemblyForContext.class,0);
		}
		public AssemblyIfContext assemblyIf() {
			return getRuleContext(AssemblyIfContext.class,0);
		}
		public TerminalNode BreakKeyword() { return getToken(SolidityParser.BreakKeyword, 0); }
		public TerminalNode ContinueKeyword() { return getToken(SolidityParser.ContinueKeyword, 0); }
		public SubAssemblyContext subAssembly() {
			return getRuleContext(SubAssemblyContext.class,0);
		}
		public NumberLiteralContext numberLiteral() {
			return getRuleContext(NumberLiteralContext.class,0);
		}
		public TerminalNode StringLiteral() { return getToken(SolidityParser.StringLiteral, 0); }
		public TerminalNode HexLiteral() { return getToken(SolidityParser.HexLiteral, 0); }
		public AssemblyItemContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyItem; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyItem(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyItem(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyItem(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyItemContext assemblyItem() throws RecognitionException {
		AssemblyItemContext _localctx = new AssemblyItemContext(_ctx, getState());
		enterRule(_localctx, 136, RULE_assemblyItem);
		try {
			setState(923);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,85,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(906);
				identifier();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(907);
				assemblyBlock();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(908);
				assemblyExpression();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(909);
				assemblyLocalDefinition();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(910);
				assemblyAssignment();
				}
				break;
			case 6:
				enterOuterAlt(_localctx, 6);
				{
				setState(911);
				assemblyStackAssignment();
				}
				break;
			case 7:
				enterOuterAlt(_localctx, 7);
				{
				setState(912);
				labelDefinition();
				}
				break;
			case 8:
				enterOuterAlt(_localctx, 8);
				{
				setState(913);
				assemblySwitch();
				}
				break;
			case 9:
				enterOuterAlt(_localctx, 9);
				{
				setState(914);
				assemblyFunctionDefinition();
				}
				break;
			case 10:
				enterOuterAlt(_localctx, 10);
				{
				setState(915);
				assemblyFor();
				}
				break;
			case 11:
				enterOuterAlt(_localctx, 11);
				{
				setState(916);
				assemblyIf();
				}
				break;
			case 12:
				enterOuterAlt(_localctx, 12);
				{
				setState(917);
				match(BreakKeyword);
				}
				break;
			case 13:
				enterOuterAlt(_localctx, 13);
				{
				setState(918);
				match(ContinueKeyword);
				}
				break;
			case 14:
				enterOuterAlt(_localctx, 14);
				{
				setState(919);
				subAssembly();
				}
				break;
			case 15:
				enterOuterAlt(_localctx, 15);
				{
				setState(920);
				numberLiteral();
				}
				break;
			case 16:
				enterOuterAlt(_localctx, 16);
				{
				setState(921);
				match(StringLiteral);
				}
				break;
			case 17:
				enterOuterAlt(_localctx, 17);
				{
				setState(922);
				match(HexLiteral);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyExpressionContext extends ParserRuleContext {
		public AssemblyCallContext assemblyCall() {
			return getRuleContext(AssemblyCallContext.class,0);
		}
		public AssemblyLiteralContext assemblyLiteral() {
			return getRuleContext(AssemblyLiteralContext.class,0);
		}
		public AssemblyExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyExpression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyExpressionContext assemblyExpression() throws RecognitionException {
		AssemblyExpressionContext _localctx = new AssemblyExpressionContext(_ctx, getState());
		enterRule(_localctx, 138, RULE_assemblyExpression);
		try {
			setState(927);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__11:
			case T__49:
			case T__53:
			case T__57:
			case Identifier:
				enterOuterAlt(_localctx, 1);
				{
				setState(925);
				assemblyCall();
				}
				break;
			case DecimalNumber:
			case HexNumber:
			case HexLiteral:
			case StringLiteral:
				enterOuterAlt(_localctx, 2);
				{
				setState(926);
				assemblyLiteral();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyCallContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public List<AssemblyExpressionContext> assemblyExpression() {
			return getRuleContexts(AssemblyExpressionContext.class);
		}
		public AssemblyExpressionContext assemblyExpression(int i) {
			return getRuleContext(AssemblyExpressionContext.class,i);
		}
		public AssemblyCallContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyCall; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyCall(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyCall(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyCall(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyCallContext assemblyCall() throws RecognitionException {
		AssemblyCallContext _localctx = new AssemblyCallContext(_ctx, getState());
		enterRule(_localctx, 140, RULE_assemblyCall);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(933);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__49:
				{
				setState(929);
				match(T__49);
				}
				break;
			case T__53:
				{
				setState(930);
				match(T__53);
				}
				break;
			case T__57:
				{
				setState(931);
				match(T__57);
				}
				break;
			case T__11:
			case Identifier:
				{
				setState(932);
				identifier();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			setState(947);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,90,_ctx) ) {
			case 1:
				{
				setState(935);
				match(T__16);
				setState(937);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__11) | (1L << T__49) | (1L << T__53) | (1L << T__57))) != 0) || ((((_la - 103)) & ~0x3f) == 0 && ((1L << (_la - 103)) & ((1L << (DecimalNumber - 103)) | (1L << (HexNumber - 103)) | (1L << (HexLiteral - 103)) | (1L << (Identifier - 103)) | (1L << (StringLiteral - 103)))) != 0)) {
					{
					setState(936);
					assemblyExpression();
					}
				}

				setState(943);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__13) {
					{
					{
					setState(939);
					match(T__13);
					setState(940);
					assemblyExpression();
					}
					}
					setState(945);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				setState(946);
				match(T__17);
				}
				break;
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyLocalDefinitionContext extends ParserRuleContext {
		public AssemblyIdentifierOrListContext assemblyIdentifierOrList() {
			return getRuleContext(AssemblyIdentifierOrListContext.class,0);
		}
		public AssemblyExpressionContext assemblyExpression() {
			return getRuleContext(AssemblyExpressionContext.class,0);
		}
		public AssemblyLocalDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyLocalDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyLocalDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyLocalDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyLocalDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyLocalDefinitionContext assemblyLocalDefinition() throws RecognitionException {
		AssemblyLocalDefinitionContext _localctx = new AssemblyLocalDefinitionContext(_ctx, getState());
		enterRule(_localctx, 142, RULE_assemblyLocalDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(949);
			match(T__89);
			setState(950);
			assemblyIdentifierOrList();
			setState(953);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__90) {
				{
				setState(951);
				match(T__90);
				setState(952);
				assemblyExpression();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyAssignmentContext extends ParserRuleContext {
		public AssemblyIdentifierOrListContext assemblyIdentifierOrList() {
			return getRuleContext(AssemblyIdentifierOrListContext.class,0);
		}
		public AssemblyExpressionContext assemblyExpression() {
			return getRuleContext(AssemblyExpressionContext.class,0);
		}
		public AssemblyAssignmentContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyAssignment; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyAssignment(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyAssignment(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyAssignment(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyAssignmentContext assemblyAssignment() throws RecognitionException {
		AssemblyAssignmentContext _localctx = new AssemblyAssignmentContext(_ctx, getState());
		enterRule(_localctx, 144, RULE_assemblyAssignment);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(955);
			assemblyIdentifierOrList();
			setState(956);
			match(T__90);
			setState(957);
			assemblyExpression();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyIdentifierOrListContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public AssemblyIdentifierListContext assemblyIdentifierList() {
			return getRuleContext(AssemblyIdentifierListContext.class,0);
		}
		public AssemblyIdentifierOrListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyIdentifierOrList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyIdentifierOrList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyIdentifierOrList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyIdentifierOrList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyIdentifierOrListContext assemblyIdentifierOrList() throws RecognitionException {
		AssemblyIdentifierOrListContext _localctx = new AssemblyIdentifierOrListContext(_ctx, getState());
		enterRule(_localctx, 146, RULE_assemblyIdentifierOrList);
		try {
			setState(964);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__11:
			case Identifier:
				enterOuterAlt(_localctx, 1);
				{
				setState(959);
				identifier();
				}
				break;
			case T__16:
				enterOuterAlt(_localctx, 2);
				{
				setState(960);
				match(T__16);
				setState(961);
				assemblyIdentifierList();
				setState(962);
				match(T__17);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyIdentifierListContext extends ParserRuleContext {
		public List<IdentifierContext> identifier() {
			return getRuleContexts(IdentifierContext.class);
		}
		public IdentifierContext identifier(int i) {
			return getRuleContext(IdentifierContext.class,i);
		}
		public AssemblyIdentifierListContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyIdentifierList; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyIdentifierList(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyIdentifierList(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyIdentifierList(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyIdentifierListContext assemblyIdentifierList() throws RecognitionException {
		AssemblyIdentifierListContext _localctx = new AssemblyIdentifierListContext(_ctx, getState());
		enterRule(_localctx, 148, RULE_assemblyIdentifierList);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(966);
			identifier();
			setState(971);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__13) {
				{
				{
				setState(967);
				match(T__13);
				setState(968);
				identifier();
				}
				}
				setState(973);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyStackAssignmentContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public AssemblyStackAssignmentContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyStackAssignment; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyStackAssignment(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyStackAssignment(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyStackAssignment(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyStackAssignmentContext assemblyStackAssignment() throws RecognitionException {
		AssemblyStackAssignmentContext _localctx = new AssemblyStackAssignmentContext(_ctx, getState());
		enterRule(_localctx, 150, RULE_assemblyStackAssignment);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(974);
			match(T__91);
			setState(975);
			identifier();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class LabelDefinitionContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public LabelDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_labelDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterLabelDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitLabelDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitLabelDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final LabelDefinitionContext labelDefinition() throws RecognitionException {
		LabelDefinitionContext _localctx = new LabelDefinitionContext(_ctx, getState());
		enterRule(_localctx, 152, RULE_labelDefinition);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(977);
			identifier();
			setState(978);
			match(T__65);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblySwitchContext extends ParserRuleContext {
		public AssemblyExpressionContext assemblyExpression() {
			return getRuleContext(AssemblyExpressionContext.class,0);
		}
		public List<AssemblyCaseContext> assemblyCase() {
			return getRuleContexts(AssemblyCaseContext.class);
		}
		public AssemblyCaseContext assemblyCase(int i) {
			return getRuleContext(AssemblyCaseContext.class,i);
		}
		public AssemblySwitchContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblySwitch; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblySwitch(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblySwitch(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblySwitch(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblySwitchContext assemblySwitch() throws RecognitionException {
		AssemblySwitchContext _localctx = new AssemblySwitchContext(_ctx, getState());
		enterRule(_localctx, 154, RULE_assemblySwitch);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(980);
			match(T__92);
			setState(981);
			assemblyExpression();
			setState(985);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__93 || _la==T__94) {
				{
				{
				setState(982);
				assemblyCase();
				}
				}
				setState(987);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyCaseContext extends ParserRuleContext {
		public AssemblyLiteralContext assemblyLiteral() {
			return getRuleContext(AssemblyLiteralContext.class,0);
		}
		public AssemblyBlockContext assemblyBlock() {
			return getRuleContext(AssemblyBlockContext.class,0);
		}
		public AssemblyCaseContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyCase; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyCase(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyCase(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyCase(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyCaseContext assemblyCase() throws RecognitionException {
		AssemblyCaseContext _localctx = new AssemblyCaseContext(_ctx, getState());
		enterRule(_localctx, 156, RULE_assemblyCase);
		try {
			setState(994);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__93:
				enterOuterAlt(_localctx, 1);
				{
				setState(988);
				match(T__93);
				setState(989);
				assemblyLiteral();
				setState(990);
				assemblyBlock();
				}
				break;
			case T__94:
				enterOuterAlt(_localctx, 2);
				{
				setState(992);
				match(T__94);
				setState(993);
				assemblyBlock();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyFunctionDefinitionContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public AssemblyBlockContext assemblyBlock() {
			return getRuleContext(AssemblyBlockContext.class,0);
		}
		public AssemblyIdentifierListContext assemblyIdentifierList() {
			return getRuleContext(AssemblyIdentifierListContext.class,0);
		}
		public AssemblyFunctionReturnsContext assemblyFunctionReturns() {
			return getRuleContext(AssemblyFunctionReturnsContext.class,0);
		}
		public AssemblyFunctionDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyFunctionDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyFunctionDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyFunctionDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyFunctionDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyFunctionDefinitionContext assemblyFunctionDefinition() throws RecognitionException {
		AssemblyFunctionDefinitionContext _localctx = new AssemblyFunctionDefinitionContext(_ctx, getState());
		enterRule(_localctx, 158, RULE_assemblyFunctionDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(996);
			match(T__23);
			setState(997);
			identifier();
			setState(998);
			match(T__16);
			setState(1000);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__11 || _la==Identifier) {
				{
				setState(999);
				assemblyIdentifierList();
				}
			}

			setState(1002);
			match(T__17);
			setState(1004);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__76) {
				{
				setState(1003);
				assemblyFunctionReturns();
				}
			}

			setState(1006);
			assemblyBlock();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyFunctionReturnsContext extends ParserRuleContext {
		public AssemblyIdentifierListContext assemblyIdentifierList() {
			return getRuleContext(AssemblyIdentifierListContext.class,0);
		}
		public AssemblyFunctionReturnsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyFunctionReturns; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyFunctionReturns(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyFunctionReturns(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyFunctionReturns(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyFunctionReturnsContext assemblyFunctionReturns() throws RecognitionException {
		AssemblyFunctionReturnsContext _localctx = new AssemblyFunctionReturnsContext(_ctx, getState());
		enterRule(_localctx, 160, RULE_assemblyFunctionReturns);
		try {
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(1008);
			match(T__76);
			setState(1009);
			assemblyIdentifierList();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyForContext extends ParserRuleContext {
		public List<AssemblyExpressionContext> assemblyExpression() {
			return getRuleContexts(AssemblyExpressionContext.class);
		}
		public AssemblyExpressionContext assemblyExpression(int i) {
			return getRuleContext(AssemblyExpressionContext.class,i);
		}
		public List<AssemblyBlockContext> assemblyBlock() {
			return getRuleContexts(AssemblyBlockContext.class);
		}
		public AssemblyBlockContext assemblyBlock(int i) {
			return getRuleContext(AssemblyBlockContext.class,i);
		}
		public AssemblyForContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyFor; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyFor(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyFor(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyFor(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyForContext assemblyFor() throws RecognitionException {
		AssemblyForContext _localctx = new AssemblyForContext(_ctx, getState());
		enterRule(_localctx, 162, RULE_assemblyFor);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(1011);
			match(T__19);
			setState(1014);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__12:
				{
				setState(1012);
				assemblyBlock();
				}
				break;
			case T__11:
			case T__49:
			case T__53:
			case T__57:
			case DecimalNumber:
			case HexNumber:
			case HexLiteral:
			case Identifier:
			case StringLiteral:
				{
				setState(1013);
				assemblyExpression();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			setState(1016);
			assemblyExpression();
			setState(1019);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__12:
				{
				setState(1017);
				assemblyBlock();
				}
				break;
			case T__11:
			case T__49:
			case T__53:
			case T__57:
			case DecimalNumber:
			case HexNumber:
			case HexLiteral:
			case Identifier:
			case StringLiteral:
				{
				setState(1018);
				assemblyExpression();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			setState(1021);
			assemblyBlock();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyIfContext extends ParserRuleContext {
		public AssemblyExpressionContext assemblyExpression() {
			return getRuleContext(AssemblyExpressionContext.class,0);
		}
		public AssemblyBlockContext assemblyBlock() {
			return getRuleContext(AssemblyBlockContext.class,0);
		}
		public AssemblyIfContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyIf; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyIf(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyIf(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyIf(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyIfContext assemblyIf() throws RecognitionException {
		AssemblyIfContext _localctx = new AssemblyIfContext(_ctx, getState());
		enterRule(_localctx, 164, RULE_assemblyIf);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(1023);
			match(T__44);
			setState(1024);
			assemblyExpression();
			setState(1025);
			assemblyBlock();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class AssemblyLiteralContext extends ParserRuleContext {
		public TerminalNode StringLiteral() { return getToken(SolidityParser.StringLiteral, 0); }
		public TerminalNode DecimalNumber() { return getToken(SolidityParser.DecimalNumber, 0); }
		public TerminalNode HexNumber() { return getToken(SolidityParser.HexNumber, 0); }
		public TerminalNode HexLiteral() { return getToken(SolidityParser.HexLiteral, 0); }
		public AssemblyLiteralContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_assemblyLiteral; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterAssemblyLiteral(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitAssemblyLiteral(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitAssemblyLiteral(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AssemblyLiteralContext assemblyLiteral() throws RecognitionException {
		AssemblyLiteralContext _localctx = new AssemblyLiteralContext(_ctx, getState());
		enterRule(_localctx, 166, RULE_assemblyLiteral);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(1027);
			_la = _input.LA(1);
			if ( !(((((_la - 103)) & ~0x3f) == 0 && ((1L << (_la - 103)) & ((1L << (DecimalNumber - 103)) | (1L << (HexNumber - 103)) | (1L << (HexLiteral - 103)) | (1L << (StringLiteral - 103)))) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class SubAssemblyContext extends ParserRuleContext {
		public IdentifierContext identifier() {
			return getRuleContext(IdentifierContext.class,0);
		}
		public AssemblyBlockContext assemblyBlock() {
			return getRuleContext(AssemblyBlockContext.class,0);
		}
		public SubAssemblyContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_subAssembly; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterSubAssembly(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitSubAssembly(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitSubAssembly(this);
			else return visitor.visitChildren(this);
		}
	}

	public final SubAssemblyContext subAssembly() throws RecognitionException {
		SubAssemblyContext _localctx = new SubAssemblyContext(_ctx, getState());
		enterRule(_localctx, 168, RULE_subAssembly);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(1029);
			match(T__47);
			setState(1030);
			identifier();
			setState(1031);
			assemblyBlock();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TupleExpressionContext extends ParserRuleContext {
		public List<ExpressionContext> expression() {
			return getRuleContexts(ExpressionContext.class);
		}
		public ExpressionContext expression(int i) {
			return getRuleContext(ExpressionContext.class,i);
		}
		public TupleExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_tupleExpression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterTupleExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitTupleExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitTupleExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TupleExpressionContext tupleExpression() throws RecognitionException {
		TupleExpressionContext _localctx = new TupleExpressionContext(_ctx, getState());
		enterRule(_localctx, 170, RULE_tupleExpression);
		int _la;
		try {
			setState(1059);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case T__16:
				enterOuterAlt(_localctx, 1);
				{
				setState(1033);
				match(T__16);
				{
				setState(1035);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__11) | (1L << T__16) | (1L << T__34) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57) | (1L << T__58) | (1L << T__59) | (1L << T__60))) != 0) || ((((_la - 82)) & ~0x3f) == 0 && ((1L << (_la - 82)) & ((1L << (T__81 - 82)) | (1L << (T__82 - 82)) | (1L << (T__83 - 82)) | (1L << (T__84 - 82)) | (1L << (T__85 - 82)) | (1L << (T__86 - 82)) | (1L << (Int - 82)) | (1L << (Uint - 82)) | (1L << (Byte - 82)) | (1L << (Fixed - 82)) | (1L << (Ufixed - 82)) | (1L << (BooleanLiteral - 82)) | (1L << (DecimalNumber - 82)) | (1L << (HexNumber - 82)) | (1L << (HexLiteral - 82)) | (1L << (Identifier - 82)) | (1L << (StringLiteral - 82)) | (1L << (PLUS - 82)) | (1L << (MINUS - 82)) | (1L << (NOT - 82)) | (1L << (INC - 82)) | (1L << (DEC - 82)))) != 0)) {
					{
					setState(1034);
					expression(0);
					}
				}

				setState(1043);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__13) {
					{
					{
					setState(1037);
					match(T__13);
					setState(1039);
					_errHandler.sync(this);
					_la = _input.LA(1);
					if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__11) | (1L << T__16) | (1L << T__34) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57) | (1L << T__58) | (1L << T__59) | (1L << T__60))) != 0) || ((((_la - 82)) & ~0x3f) == 0 && ((1L << (_la - 82)) & ((1L << (T__81 - 82)) | (1L << (T__82 - 82)) | (1L << (T__83 - 82)) | (1L << (T__84 - 82)) | (1L << (T__85 - 82)) | (1L << (T__86 - 82)) | (1L << (Int - 82)) | (1L << (Uint - 82)) | (1L << (Byte - 82)) | (1L << (Fixed - 82)) | (1L << (Ufixed - 82)) | (1L << (BooleanLiteral - 82)) | (1L << (DecimalNumber - 82)) | (1L << (HexNumber - 82)) | (1L << (HexLiteral - 82)) | (1L << (Identifier - 82)) | (1L << (StringLiteral - 82)) | (1L << (PLUS - 82)) | (1L << (MINUS - 82)) | (1L << (NOT - 82)) | (1L << (INC - 82)) | (1L << (DEC - 82)))) != 0)) {
						{
						setState(1038);
						expression(0);
						}
					}

					}
					}
					setState(1045);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
				setState(1046);
				match(T__17);
				}
				break;
			case T__34:
				enterOuterAlt(_localctx, 2);
				{
				setState(1047);
				match(T__34);
				setState(1056);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << T__3) | (1L << T__11) | (1L << T__16) | (1L << T__34) | (1L << T__52) | (1L << T__53) | (1L << T__54) | (1L << T__55) | (1L << T__56) | (1L << T__57) | (1L << T__58) | (1L << T__59) | (1L << T__60))) != 0) || ((((_la - 82)) & ~0x3f) == 0 && ((1L << (_la - 82)) & ((1L << (T__81 - 82)) | (1L << (T__82 - 82)) | (1L << (T__83 - 82)) | (1L << (T__84 - 82)) | (1L << (T__85 - 82)) | (1L << (T__86 - 82)) | (1L << (Int - 82)) | (1L << (Uint - 82)) | (1L << (Byte - 82)) | (1L << (Fixed - 82)) | (1L << (Ufixed - 82)) | (1L << (BooleanLiteral - 82)) | (1L << (DecimalNumber - 82)) | (1L << (HexNumber - 82)) | (1L << (HexLiteral - 82)) | (1L << (Identifier - 82)) | (1L << (StringLiteral - 82)) | (1L << (PLUS - 82)) | (1L << (MINUS - 82)) | (1L << (NOT - 82)) | (1L << (INC - 82)) | (1L << (DEC - 82)))) != 0)) {
					{
					setState(1048);
					expression(0);
					setState(1053);
					_errHandler.sync(this);
					_la = _input.LA(1);
					while (_la==T__13) {
						{
						{
						setState(1049);
						match(T__13);
						setState(1050);
						expression(0);
						}
						}
						setState(1055);
						_errHandler.sync(this);
						_la = _input.LA(1);
					}
					}
				}

				setState(1058);
				match(T__35);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ElementaryTypeNameExpressionContext extends ParserRuleContext {
		public ElementaryTypeNameContext elementaryTypeName() {
			return getRuleContext(ElementaryTypeNameContext.class,0);
		}
		public ElementaryTypeNameExpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_elementaryTypeNameExpression; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterElementaryTypeNameExpression(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitElementaryTypeNameExpression(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitElementaryTypeNameExpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ElementaryTypeNameExpressionContext elementaryTypeNameExpression() throws RecognitionException {
		ElementaryTypeNameExpressionContext _localctx = new ElementaryTypeNameExpressionContext(_ctx, getState());
		enterRule(_localctx, 172, RULE_elementaryTypeNameExpression);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(1061);
			elementaryTypeName();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class NumberLiteralContext extends ParserRuleContext {
		public TerminalNode DecimalNumber() { return getToken(SolidityParser.DecimalNumber, 0); }
		public TerminalNode HexNumber() { return getToken(SolidityParser.HexNumber, 0); }
		public TerminalNode NumberUnit() { return getToken(SolidityParser.NumberUnit, 0); }
		public NumberLiteralContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_numberLiteral; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterNumberLiteral(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitNumberLiteral(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitNumberLiteral(this);
			else return visitor.visitChildren(this);
		}
	}

	public final NumberLiteralContext numberLiteral() throws RecognitionException {
		NumberLiteralContext _localctx = new NumberLiteralContext(_ctx, getState());
		enterRule(_localctx, 174, RULE_numberLiteral);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(1063);
			_la = _input.LA(1);
			if ( !(_la==DecimalNumber || _la==HexNumber) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			setState(1065);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,106,_ctx) ) {
			case 1:
				{
				setState(1064);
				match(NumberUnit);
				}
				break;
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class IdentifierContext extends ParserRuleContext {
		public TerminalNode Identifier() { return getToken(SolidityParser.Identifier, 0); }
		public IdentifierContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_identifier; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).enterIdentifier(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof SolidityListener ) ((SolidityListener)listener).exitIdentifier(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof SolidityVisitor ) return ((SolidityVisitor<? extends T>)visitor).visitIdentifier(this);
			else return visitor.visitChildren(this);
		}
	}

	public final IdentifierContext identifier() throws RecognitionException {
		IdentifierContext _localctx = new IdentifierContext(_ctx, getState());
		enterRule(_localctx, 176, RULE_identifier);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(1067);
			_la = _input.LA(1);
			if ( !(_la==T__11 || _la==Identifier) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 33:
			return typeName_sempred((TypeNameContext)_localctx, predIndex);
		case 59:
			return expression_sempred((ExpressionContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean typeName_sempred(TypeNameContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 2);
		}
		return true;
	}
	private boolean expression_sempred(ExpressionContext _localctx, int predIndex) {
		switch (predIndex) {
		case 1:
			return precpred(_ctx, 25);
		case 2:
			return precpred(_ctx, 24);
		case 3:
			return precpred(_ctx, 23);
		case 4:
			return precpred(_ctx, 22);
		case 5:
			return precpred(_ctx, 21);
		case 6:
			return precpred(_ctx, 20);
		case 7:
			return precpred(_ctx, 19);
		case 8:
			return precpred(_ctx, 18);
		case 9:
			return precpred(_ctx, 17);
		case 10:
			return precpred(_ctx, 16);
		case 11:
			return precpred(_ctx, 15);
		case 12:
			return precpred(_ctx, 14);
		case 13:
			return precpred(_ctx, 13);
		case 14:
			return precpred(_ctx, 11);
		case 15:
			return precpred(_ctx, 10);
		case 16:
			return precpred(_ctx, 9);
		case 17:
			return precpred(_ctx, 36);
		case 18:
			return precpred(_ctx, 34);
		case 19:
			return precpred(_ctx, 33);
		case 20:
			return precpred(_ctx, 32);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\u0097\u0430\4\2\t"+
		"\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\4"+
		",\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63\4\64\t"+
		"\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\49\t9\4:\t:\4;\t;\4<\t<\4=\t="+
		"\4>\t>\4?\t?\4@\t@\4A\tA\4B\tB\4C\tC\4D\tD\4E\tE\4F\tF\4G\tG\4H\tH\4I"+
		"\tI\4J\tJ\4K\tK\4L\tL\4M\tM\4N\tN\4O\tO\4P\tP\4Q\tQ\4R\tR\4S\tS\4T\tT"+
		"\4U\tU\4V\tV\4W\tW\4X\tX\4Y\tY\4Z\tZ\3\2\3\2\3\2\3\2\7\2\u00b9\n\2\f\2"+
		"\16\2\u00bc\13\2\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\5\3\5\5\5\u00c9"+
		"\n\5\3\6\3\6\5\6\u00cd\n\6\3\7\3\7\3\b\5\b\u00d2\n\b\3\b\3\b\3\t\3\t\3"+
		"\t\5\t\u00d9\n\t\3\n\3\n\3\n\3\n\5\n\u00df\n\n\3\n\3\n\3\n\3\n\5\n\u00e5"+
		"\n\n\3\n\3\n\5\n\u00e9\n\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\7\n\u00f3\n"+
		"\n\f\n\16\n\u00f6\13\n\3\n\3\n\3\n\3\n\3\n\5\n\u00fd\n\n\3\13\5\13\u0100"+
		"\n\13\3\13\3\13\3\13\3\13\3\13\3\13\7\13\u0108\n\13\f\13\16\13\u010b\13"+
		"\13\5\13\u010d\n\13\3\13\3\13\7\13\u0111\n\13\f\13\16\13\u0114\13\13\3"+
		"\13\3\13\3\f\3\f\3\f\3\f\3\f\7\f\u011d\n\f\f\f\16\f\u0120\13\f\3\f\3\f"+
		"\5\f\u0124\n\f\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\5\r\u012e\n\r\3\16\3\16"+
		"\7\16\u0132\n\16\f\16\16\16\u0135\13\16\3\16\3\16\3\16\5\16\u013a\n\16"+
		"\3\16\3\16\3\17\3\17\3\17\3\17\3\17\5\17\u0143\n\17\3\17\3\17\3\20\3\20"+
		"\3\20\3\20\3\20\3\20\3\20\3\20\7\20\u014f\n\20\f\20\16\20\u0152\13\20"+
		"\5\20\u0154\n\20\3\20\3\20\3\21\3\21\3\21\3\21\3\21\3\22\3\22\3\22\5\22"+
		"\u0160\n\22\3\22\5\22\u0163\n\22\3\22\3\22\3\23\3\23\3\23\5\23\u016a\n"+
		"\23\3\23\5\23\u016d\n\23\3\24\3\24\5\24\u0171\n\24\3\24\3\24\3\24\5\24"+
		"\u0176\n\24\3\24\3\24\5\24\u017a\n\24\3\25\3\25\3\25\3\26\3\26\3\26\3"+
		"\26\3\26\3\26\3\26\3\26\7\26\u0187\n\26\f\26\16\26\u018a\13\26\3\27\3"+
		"\27\3\27\3\27\5\27\u0190\n\27\3\27\3\27\3\30\3\30\3\31\3\31\3\31\3\31"+
		"\5\31\u019a\n\31\3\31\3\31\7\31\u019e\n\31\f\31\16\31\u01a1\13\31\3\31"+
		"\3\31\3\32\7\32\u01a6\n\32\f\32\16\32\u01a9\13\32\3\33\3\33\3\33\3\33"+
		"\3\33\3\33\3\33\3\33\3\33\3\33\3\33\3\33\3\33\3\33\3\33\3\33\3\33\3\33"+
		"\7\33\u01bd\n\33\f\33\16\33\u01c0\13\33\3\33\3\33\3\33\3\33\3\33\5\33"+
		"\u01c7\n\33\3\34\3\34\3\34\3\34\7\34\u01cd\n\34\f\34\16\34\u01d0\13\34"+
		"\5\34\u01d2\n\34\3\34\3\34\3\35\3\35\5\35\u01d8\n\35\3\35\5\35\u01db\n"+
		"\35\3\36\3\36\3\36\3\36\7\36\u01e1\n\36\f\36\16\36\u01e4\13\36\5\36\u01e6"+
		"\n\36\3\36\3\36\3\37\3\37\5\37\u01ec\n\37\3\37\5\37\u01ef\n\37\3 \3 \3"+
		" \3 \7 \u01f5\n \f \16 \u01f8\13 \5 \u01fa\n \3 \3 \3!\3!\5!\u0200\n!"+
		"\3\"\3\"\3\"\5\"\u0205\n\"\3\"\3\"\3#\3#\3#\3#\3#\5#\u020e\n#\3#\3#\3"+
		"#\5#\u0213\n#\3#\7#\u0216\n#\f#\16#\u0219\13#\3$\3$\3$\7$\u021e\n$\f$"+
		"\16$\u0221\13$\3%\3%\3%\3%\3%\3%\3%\3&\3&\3&\3&\3&\7&\u022f\n&\f&\16&"+
		"\u0232\13&\3&\3&\5&\u0236\n&\3\'\3\'\3(\3(\3)\3)\7)\u023e\n)\f)\16)\u0241"+
		"\13)\3)\3)\3*\3*\3*\3+\3+\3+\3+\3+\3+\3+\3+\3+\3+\3+\3+\3+\3+\5+\u0256"+
		"\n+\3,\3,\3-\3-\3-\3.\3.\3.\3.\3.\3.\3.\5.\u0264\n.\3/\3/\3/\3/\3/\3/"+
		"\3\60\3\60\5\60\u026e\n\60\3\61\3\61\3\61\3\61\5\61\u0274\n\61\3\61\5"+
		"\61\u0277\n\61\3\61\3\61\5\61\u027b\n\61\3\61\3\61\3\61\3\62\3\62\5\62"+
		"\u0282\n\62\3\62\3\62\3\63\3\63\3\63\3\63\3\63\3\63\3\63\3\63\3\64\3\64"+
		"\3\64\3\65\3\65\3\65\3\66\3\66\5\66\u0296\n\66\3\66\3\66\3\67\3\67\3\67"+
		"\38\38\38\38\39\39\39\39\39\39\39\59\u02a8\n9\39\39\59\u02ac\n9\39\39"+
		"\3:\5:\u02b1\n:\3:\3:\5:\u02b5\n:\7:\u02b7\n:\f:\16:\u02ba\13:\3;\3;\5"+
		";\u02be\n;\3;\7;\u02c1\n;\f;\16;\u02c4\13;\3;\5;\u02c7\n;\3;\3;\3<\3<"+
		"\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3="+
		"\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3="+
		"\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\5=\u0305\n=\3=\3=\3=\3=\3=\3=\3=\3=\3="+
		"\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3="+
		"\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3="+
		"\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\3=\7=\u0349\n=\f=\16=\u034c\13=\3>\3>\3"+
		">\3>\3>\3>\3>\5>\u0355\n>\3?\3?\3?\3?\3?\3?\3?\3@\3@\3@\7@\u0361\n@\f"+
		"@\16@\u0364\13@\3A\3A\3A\7A\u0369\nA\fA\16A\u036c\13A\3A\5A\u036f\nA\3"+
		"B\3B\3B\3B\3C\3C\5C\u0377\nC\3C\3C\5C\u037b\nC\5C\u037d\nC\3D\3D\3D\3"+
		"D\3D\3E\3E\7E\u0386\nE\fE\16E\u0389\13E\3E\3E\3F\3F\3F\3F\3F\3F\3F\3F"+
		"\3F\3F\3F\3F\3F\3F\3F\3F\3F\5F\u039e\nF\3G\3G\5G\u03a2\nG\3H\3H\3H\3H"+
		"\5H\u03a8\nH\3H\3H\5H\u03ac\nH\3H\3H\7H\u03b0\nH\fH\16H\u03b3\13H\3H\5"+
		"H\u03b6\nH\3I\3I\3I\3I\5I\u03bc\nI\3J\3J\3J\3J\3K\3K\3K\3K\3K\5K\u03c7"+
		"\nK\3L\3L\3L\7L\u03cc\nL\fL\16L\u03cf\13L\3M\3M\3M\3N\3N\3N\3O\3O\3O\7"+
		"O\u03da\nO\fO\16O\u03dd\13O\3P\3P\3P\3P\3P\3P\5P\u03e5\nP\3Q\3Q\3Q\3Q"+
		"\5Q\u03eb\nQ\3Q\3Q\5Q\u03ef\nQ\3Q\3Q\3R\3R\3R\3S\3S\3S\5S\u03f9\nS\3S"+
		"\3S\3S\5S\u03fe\nS\3S\3S\3T\3T\3T\3T\3U\3U\3V\3V\3V\3V\3W\3W\5W\u040e"+
		"\nW\3W\3W\5W\u0412\nW\7W\u0414\nW\fW\16W\u0417\13W\3W\3W\3W\3W\3W\7W\u041e"+
		"\nW\fW\16W\u0421\13W\5W\u0423\nW\3W\5W\u0426\nW\3X\3X\3Y\3Y\5Y\u042c\n"+
		"Y\3Z\3Z\3Z\2\4Dx[\2\4\6\b\n\f\16\20\22\24\26\30\32\34\36 \"$&(*,.\60\62"+
		"\64\668:<>@BDFHJLNPRTVXZ\\^`bdfhjlnprtvxz|~\u0080\u0082\u0084\u0086\u0088"+
		"\u008a\u008c\u008e\u0090\u0092\u0094\u0096\u0098\u009a\u009c\u009e\u00a0"+
		"\u00a2\u00a4\u00a6\u00a8\u00aa\u00ac\u00ae\u00b0\u00b2\2\25\3\2\5\13\5"+
		"\2sswwyy\6\2qquuxx|}\4\2zz\u0080\u0080\3\2*,\5\2qq{{~\177\4\2\67<bf\3"+
		"\2\u0091\u0092\3\2\u0083\u0084\3\2>?\3\2\u0085\u0087\3\2\u0088\u0089\3"+
		"\2\7\n\3\2AB\4\2\13\13EN\3\2Z[\5\2ijll\u0082\u0082\3\2ij\4\2\16\16\u0081"+
		"\u0081\2\u049c\2\u00ba\3\2\2\2\4\u00bf\3\2\2\2\6\u00c4\3\2\2\2\b\u00c8"+
		"\3\2\2\2\n\u00ca\3\2\2\2\f\u00ce\3\2\2\2\16\u00d1\3\2\2\2\20\u00d5\3\2"+
		"\2\2\22\u00fc\3\2\2\2\24\u00ff\3\2\2\2\26\u0117\3\2\2\2\30\u012d\3\2\2"+
		"\2\32\u012f\3\2\2\2\34\u013d\3\2\2\2\36\u0146\3\2\2\2 \u0157\3\2\2\2\""+
		"\u015c\3\2\2\2$\u0166\3\2\2\2&\u016e\3\2\2\2(\u017b\3\2\2\2*\u0188\3\2"+
		"\2\2,\u018b\3\2\2\2.\u0193\3\2\2\2\60\u0195\3\2\2\2\62\u01a7\3\2\2\2\64"+
		"\u01c6\3\2\2\2\66\u01c8\3\2\2\28\u01d5\3\2\2\2:\u01dc\3\2\2\2<\u01e9\3"+
		"\2\2\2>\u01f0\3\2\2\2@\u01fd\3\2\2\2B\u0201\3\2\2\2D\u020d\3\2\2\2F\u021a"+
		"\3\2\2\2H\u0222\3\2\2\2J\u0229\3\2\2\2L\u0237\3\2\2\2N\u0239\3\2\2\2P"+
		"\u023b\3\2\2\2R\u0244\3\2\2\2T\u0255\3\2\2\2V\u0257\3\2\2\2X\u0259\3\2"+
		"\2\2Z\u025c\3\2\2\2\\\u0265\3\2\2\2^\u026d\3\2\2\2`\u026f\3\2\2\2b\u027f"+
		"\3\2\2\2d\u0285\3\2\2\2f\u028d\3\2\2\2h\u0290\3\2\2\2j\u0293\3\2\2\2l"+
		"\u0299\3\2\2\2n\u029c\3\2\2\2p\u02a7\3\2\2\2r\u02b0\3\2\2\2t\u02bb\3\2"+
		"\2\2v\u02ca\3\2\2\2x\u0304\3\2\2\2z\u0354\3\2\2\2|\u0356\3\2\2\2~\u035d"+
		"\3\2\2\2\u0080\u0365\3\2\2\2\u0082\u0370\3\2\2\2\u0084\u037c\3\2\2\2\u0086"+
		"\u037e\3\2\2\2\u0088\u0383\3\2\2\2\u008a\u039d\3\2\2\2\u008c\u03a1\3\2"+
		"\2\2\u008e\u03a7\3\2\2\2\u0090\u03b7\3\2\2\2\u0092\u03bd\3\2\2\2\u0094"+
		"\u03c6\3\2\2\2\u0096\u03c8\3\2\2\2\u0098\u03d0\3\2\2\2\u009a\u03d3\3\2"+
		"\2\2\u009c\u03d6\3\2\2\2\u009e\u03e4\3\2\2\2\u00a0\u03e6\3\2\2\2\u00a2"+
		"\u03f2\3\2\2\2\u00a4\u03f5\3\2\2\2\u00a6\u0401\3\2\2\2\u00a8\u0405\3\2"+
		"\2\2\u00aa\u0407\3\2\2\2\u00ac\u0425\3\2\2\2\u00ae\u0427\3\2\2\2\u00b0"+
		"\u0429\3\2\2\2\u00b2\u042d\3\2\2\2\u00b4\u00b9\5\4\3\2\u00b5\u00b9\5\22"+
		"\n\2\u00b6\u00b9\5\24\13\2\u00b7\u00b9\5\36\20\2\u00b8\u00b4\3\2\2\2\u00b8"+
		"\u00b5\3\2\2\2\u00b8\u00b6\3\2\2\2\u00b8\u00b7\3\2\2\2\u00b9\u00bc\3\2"+
		"\2\2\u00ba\u00b8\3\2\2\2\u00ba\u00bb\3\2\2\2\u00bb\u00bd\3\2\2\2\u00bc"+
		"\u00ba\3\2\2\2\u00bd\u00be\7\2\2\3\u00be\3\3\2\2\2\u00bf\u00c0\7\3\2\2"+
		"\u00c0\u00c1\5\6\4\2\u00c1\u00c2\5\b\5\2\u00c2\u00c3\7\4\2\2\u00c3\5\3"+
		"\2\2\2\u00c4\u00c5\5\u00b2Z\2\u00c5\7\3\2\2\2\u00c6\u00c9\5\n\6\2\u00c7"+
		"\u00c9\5x=\2\u00c8\u00c6\3\2\2\2\u00c8\u00c7\3\2\2\2\u00c9\t\3\2\2\2\u00ca"+
		"\u00cc\5\16\b\2\u00cb\u00cd\5\16\b\2\u00cc\u00cb\3\2\2\2\u00cc\u00cd\3"+
		"\2\2\2\u00cd\13\3\2\2\2\u00ce\u00cf\t\2\2\2\u00cf\r\3\2\2\2\u00d0\u00d2"+
		"\5\f\7\2\u00d1\u00d0\3\2\2\2\u00d1\u00d2\3\2\2\2\u00d2\u00d3\3\2\2\2\u00d3"+
		"\u00d4\7g\2\2\u00d4\17\3\2\2\2\u00d5\u00d8\5\u00b2Z\2\u00d6\u00d7\7\f"+
		"\2\2\u00d7\u00d9\5\u00b2Z\2\u00d8\u00d6\3\2\2\2\u00d8\u00d9\3\2\2\2\u00d9"+
		"\21\3\2\2\2\u00da\u00db\7\r\2\2\u00db\u00de\7\u0082\2\2\u00dc\u00dd\7"+
		"\f\2\2\u00dd\u00df\5\u00b2Z\2\u00de\u00dc\3\2\2\2\u00de\u00df\3\2\2\2"+
		"\u00df\u00e0\3\2\2\2\u00e0\u00fd\7\4\2\2\u00e1\u00e4\7\r\2\2\u00e2\u00e5"+
		"\7\u0085\2\2\u00e3\u00e5\5\u00b2Z\2\u00e4\u00e2\3\2\2\2\u00e4\u00e3\3"+
		"\2\2\2\u00e5\u00e8\3\2\2\2\u00e6\u00e7\7\f\2\2\u00e7\u00e9\5\u00b2Z\2"+
		"\u00e8\u00e6\3\2\2\2\u00e8\u00e9\3\2\2\2\u00e9\u00ea\3\2\2\2\u00ea\u00eb"+
		"\7\16\2\2\u00eb\u00ec\7\u0082\2\2\u00ec\u00fd\7\4\2\2\u00ed\u00ee\7\r"+
		"\2\2\u00ee\u00ef\7\17\2\2\u00ef\u00f4\5\20\t\2\u00f0\u00f1\7\20\2\2\u00f1"+
		"\u00f3\5\20\t\2\u00f2\u00f0\3\2\2\2\u00f3\u00f6\3\2\2\2\u00f4\u00f2\3"+
		"\2\2\2\u00f4\u00f5\3\2\2\2\u00f5\u00f7\3\2\2\2\u00f6\u00f4\3\2\2\2\u00f7"+
		"\u00f8\7\21\2\2\u00f8\u00f9\7\16\2\2\u00f9\u00fa\7\u0082\2\2\u00fa\u00fb"+
		"\7\4\2\2\u00fb\u00fd\3\2\2\2\u00fc\u00da\3\2\2\2\u00fc\u00e1\3\2\2\2\u00fc"+
		"\u00ed\3\2\2\2\u00fd\23\3\2\2\2\u00fe\u0100\7n\2\2\u00ff\u00fe\3\2\2\2"+
		"\u00ff\u0100\3\2\2\2\u0100\u0101\3\2\2\2\u0101\u0102\t\3\2\2\u0102\u010c"+
		"\5\u00b2Z\2\u0103\u0104\7\22\2\2\u0104\u0109\5\26\f\2\u0105\u0106\7\20"+
		"\2\2\u0106\u0108\5\26\f\2\u0107\u0105\3\2\2\2\u0108\u010b\3\2\2\2\u0109"+
		"\u0107\3\2\2\2\u0109\u010a\3\2\2\2\u010a\u010d\3\2\2\2\u010b\u0109\3\2"+
		"\2\2\u010c\u0103\3\2\2\2\u010c\u010d\3\2\2\2\u010d\u010e\3\2\2\2\u010e"+
		"\u0112\7\17\2\2\u010f\u0111\5\30\r\2\u0110\u010f\3\2\2\2\u0111\u0114\3"+
		"\2\2\2\u0112\u0110\3\2\2\2\u0112\u0113\3\2\2\2\u0113\u0115\3\2\2\2\u0114"+
		"\u0112\3\2\2\2\u0115\u0116\7\21\2\2\u0116\25\3\2\2\2\u0117\u0123\5F$\2"+
		"\u0118\u0119\7\23\2\2\u0119\u011e\5x=\2\u011a\u011b\7\20\2\2\u011b\u011d"+
		"\5x=\2\u011c\u011a\3\2\2\2\u011d\u0120\3\2\2\2\u011e\u011c\3\2\2\2\u011e"+
		"\u011f\3\2\2\2\u011f\u0121\3\2\2\2\u0120\u011e\3\2\2\2\u0121\u0122\7\24"+
		"\2\2\u0122\u0124\3\2\2\2\u0123\u0118\3\2\2\2\u0123\u0124\3\2\2\2\u0124"+
		"\27\3\2\2\2\u0125\u012e\5\32\16\2\u0126\u012e\5\34\17\2\u0127\u012e\5"+
		"\36\20\2\u0128\u012e\5 \21\2\u0129\u012e\5\"\22\2\u012a\u012e\5&\24\2"+
		"\u012b\u012e\5,\27\2\u012c\u012e\5\60\31\2\u012d\u0125\3\2\2\2\u012d\u0126"+
		"\3\2\2\2\u012d\u0127\3\2\2\2\u012d\u0128\3\2\2\2\u012d\u0129\3\2\2\2\u012d"+
		"\u012a\3\2\2\2\u012d\u012b\3\2\2\2\u012d\u012c\3\2\2\2\u012e\31\3\2\2"+
		"\2\u012f\u0133\5D#\2\u0130\u0132\t\4\2\2\u0131\u0130\3\2\2\2\u0132\u0135"+
		"\3\2\2\2\u0133\u0131\3\2\2\2\u0133\u0134\3\2\2\2\u0134\u0136\3\2\2\2\u0135"+
		"\u0133\3\2\2\2\u0136\u0139\5\u00b2Z\2\u0137\u0138\7\13\2\2\u0138\u013a"+
		"\5x=\2\u0139\u0137\3\2\2\2\u0139\u013a\3\2\2\2\u013a\u013b\3\2\2\2\u013b"+
		"\u013c\7\4\2\2\u013c\33\3\2\2\2\u013d\u013e\7\25\2\2\u013e\u013f\5\u00b2"+
		"Z\2\u013f\u0142\7\26\2\2\u0140\u0143\7\u0085\2\2\u0141\u0143\5D#\2\u0142"+
		"\u0140\3\2\2\2\u0142\u0141\3\2\2\2\u0143\u0144\3\2\2\2\u0144\u0145\7\4"+
		"\2\2\u0145\35\3\2\2\2\u0146\u0147\7\27\2\2\u0147\u0148\5\u00b2Z\2\u0148"+
		"\u0153\7\17\2\2\u0149\u014a\5B\"\2\u014a\u0150\7\4\2\2\u014b\u014c\5B"+
		"\"\2\u014c\u014d\7\4\2\2\u014d\u014f\3\2\2\2\u014e\u014b\3\2\2\2\u014f"+
		"\u0152\3\2\2\2\u0150\u014e\3\2\2\2\u0150\u0151\3\2\2\2\u0151\u0154\3\2"+
		"\2\2\u0152\u0150\3\2\2\2\u0153\u0149\3\2\2\2\u0153\u0154\3\2\2\2\u0154"+
		"\u0155\3\2\2\2\u0155\u0156\7\21\2\2\u0156\37\3\2\2\2\u0157\u0158\7\30"+
		"\2\2\u0158\u0159\5\66\34\2\u0159\u015a\5*\26\2\u015a\u015b\5P)\2\u015b"+
		"!\3\2\2\2\u015c\u015d\7\31\2\2\u015d\u015f\5\u00b2Z\2\u015e\u0160\5\66"+
		"\34\2\u015f\u015e\3\2\2\2\u015f\u0160\3\2\2\2\u0160\u0162\3\2\2\2\u0161"+
		"\u0163\t\5\2\2\u0162\u0161\3\2\2\2\u0162\u0163\3\2\2\2\u0163\u0164\3\2"+
		"\2\2\u0164\u0165\5P)\2\u0165#\3\2\2\2\u0166\u016c\5\u00b2Z\2\u0167\u0169"+
		"\7\23\2\2\u0168\u016a\5~@\2\u0169\u0168\3\2\2\2\u0169\u016a\3\2\2\2\u016a"+
		"\u016b\3\2\2\2\u016b\u016d\7\24\2\2\u016c\u0167\3\2\2\2\u016c\u016d\3"+
		"\2\2\2\u016d%\3\2\2\2\u016e\u0170\7\32\2\2\u016f\u0171\5\u00b2Z\2\u0170"+
		"\u016f\3\2\2\2\u0170\u0171\3\2\2\2\u0171\u0172\3\2\2\2\u0172\u0173\5\66"+
		"\34\2\u0173\u0175\5*\26\2\u0174\u0176\5(\25\2\u0175\u0174\3\2\2\2\u0175"+
		"\u0176\3\2\2\2\u0176\u0179\3\2\2\2\u0177\u017a\7\4\2\2\u0178\u017a\5P"+
		")\2\u0179\u0177\3\2\2\2\u0179\u0178\3\2\2\2\u017a\'\3\2\2\2\u017b\u017c"+
		"\7\33\2\2\u017c\u017d\5\66\34\2\u017d)\3\2\2\2\u017e\u0187\5$\23\2\u017f"+
		"\u0187\5N(\2\u0180\u0187\7t\2\2\u0181\u0187\7}\2\2\u0182\u0187\7x\2\2"+
		"\u0183\u0187\7|\2\2\u0184\u0187\7\u0080\2\2\u0185\u0187\7z\2\2\u0186\u017e"+
		"\3\2\2\2\u0186\u017f\3\2\2\2\u0186\u0180\3\2\2\2\u0186\u0181\3\2\2\2\u0186"+
		"\u0182\3\2\2\2\u0186\u0183\3\2\2\2\u0186\u0184\3\2\2\2\u0186\u0185\3\2"+
		"\2\2\u0187\u018a\3\2\2\2\u0188\u0186\3\2\2\2\u0188\u0189\3\2\2\2\u0189"+
		"+\3\2\2\2\u018a\u0188\3\2\2\2\u018b\u018c\7\34\2\2\u018c\u018d\5\u00b2"+
		"Z\2\u018d\u018f\5:\36\2\u018e\u0190\7o\2\2\u018f\u018e\3\2\2\2\u018f\u0190"+
		"\3\2\2\2\u0190\u0191\3\2\2\2\u0191\u0192\7\4\2\2\u0192-\3\2\2\2\u0193"+
		"\u0194\5\u00b2Z\2\u0194/\3\2\2\2\u0195\u0196\7\35\2\2\u0196\u0197\5\u00b2"+
		"Z\2\u0197\u0199\7\17\2\2\u0198\u019a\5.\30\2\u0199\u0198\3\2\2\2\u0199"+
		"\u019a\3\2\2\2\u019a\u019f\3\2\2\2\u019b\u019c\7\20\2\2\u019c\u019e\5"+
		".\30\2\u019d\u019b\3\2\2\2\u019e\u01a1\3\2\2\2\u019f\u019d\3\2\2\2\u019f"+
		"\u01a0\3\2\2\2\u01a0\u01a2\3\2\2\2\u01a1\u019f\3\2\2\2\u01a2\u01a3\7\21"+
		"\2\2\u01a3\61\3\2\2\2\u01a4\u01a6\5\64\33\2\u01a5\u01a4\3\2\2\2\u01a6"+
		"\u01a9\3\2\2\2\u01a7\u01a5\3\2\2\2\u01a7\u01a8\3\2\2\2\u01a8\63\3\2\2"+
		"\2\u01a9\u01a7\3\2\2\2\u01aa\u01ab\7\36\2\2\u01ab\u01c7\5X-\2\u01ac\u01ad"+
		"\7\37\2\2\u01ad\u01c7\5X-\2\u01ae\u01af\7 \2\2\u01af\u01c7\5X-\2\u01b0"+
		"\u01b1\7!\2\2\u01b1\u01c7\5X-\2\u01b2\u01b3\7\"\2\2\u01b3\u01b4\5D#\2"+
		"\u01b4\u01b5\7\u0081\2\2\u01b5\u01b6\7\4\2\2\u01b6\u01b7\5X-\2\u01b7\u01c7"+
		"\3\2\2\2\u01b8\u01b9\7#\2\2\u01b9\u01be\5x=\2\u01ba\u01bb\7\20\2\2\u01bb"+
		"\u01bd\5x=\2\u01bc\u01ba\3\2\2\2\u01bd\u01c0\3\2\2\2\u01be\u01bc\3\2\2"+
		"\2\u01be\u01bf\3\2\2\2\u01bf\u01c7\3\2\2\2\u01c0\u01be\3\2\2\2\u01c1\u01c2"+
		"\5\u00b2Z\2\u01c2\u01c3\7$\2\2\u01c3\u01c4\5\u00b2Z\2\u01c4\u01c5\7\4"+
		"\2\2\u01c5\u01c7\3\2\2\2\u01c6\u01aa\3\2\2\2\u01c6\u01ac\3\2\2\2\u01c6"+
		"\u01ae\3\2\2\2\u01c6\u01b0\3\2\2\2\u01c6\u01b2\3\2\2\2\u01c6\u01b8\3\2"+
		"\2\2\u01c6\u01c1\3\2\2\2\u01c7\65\3\2\2\2\u01c8\u01d1\7\23\2\2\u01c9\u01ce"+
		"\58\35\2\u01ca\u01cb\7\20\2\2\u01cb\u01cd\58\35\2\u01cc\u01ca\3\2\2\2"+
		"\u01cd\u01d0\3\2\2\2\u01ce\u01cc\3\2\2\2\u01ce\u01cf\3\2\2\2\u01cf\u01d2"+
		"\3\2\2\2\u01d0\u01ce\3\2\2\2\u01d1\u01c9\3\2\2\2\u01d1\u01d2\3\2\2\2\u01d2"+
		"\u01d3\3\2\2\2\u01d3\u01d4\7\24\2\2\u01d4\67\3\2\2\2\u01d5\u01d7\5D#\2"+
		"\u01d6\u01d8\5L\'\2\u01d7\u01d6\3\2\2\2\u01d7\u01d8\3\2\2\2\u01d8\u01da"+
		"\3\2\2\2\u01d9\u01db\5\u00b2Z\2\u01da\u01d9\3\2\2\2\u01da\u01db\3\2\2"+
		"\2\u01db9\3\2\2\2\u01dc\u01e5\7\23\2\2\u01dd\u01e2\5<\37\2\u01de\u01df"+
		"\7\20\2\2\u01df\u01e1\5<\37\2\u01e0\u01de\3\2\2\2\u01e1\u01e4\3\2\2\2"+
		"\u01e2\u01e0\3\2\2\2\u01e2\u01e3\3\2\2\2\u01e3\u01e6\3\2\2\2\u01e4\u01e2"+
		"\3\2\2\2\u01e5\u01dd\3\2\2\2\u01e5\u01e6\3\2\2\2\u01e6\u01e7\3\2\2\2\u01e7"+
		"\u01e8\7\24\2\2\u01e8;\3\2\2\2\u01e9\u01eb\5D#\2\u01ea\u01ec\7v\2\2\u01eb"+
		"\u01ea\3\2\2\2\u01eb\u01ec\3\2\2\2\u01ec\u01ee\3\2\2\2\u01ed\u01ef\5\u00b2"+
		"Z\2\u01ee\u01ed\3\2\2\2\u01ee\u01ef\3\2\2\2\u01ef=\3\2\2\2\u01f0\u01f9"+
		"\7\23\2\2\u01f1\u01f6\5@!\2\u01f2\u01f3\7\20\2\2\u01f3\u01f5\5@!\2\u01f4"+
		"\u01f2\3\2\2\2\u01f5\u01f8\3\2\2\2\u01f6\u01f4\3\2\2\2\u01f6\u01f7\3\2"+
		"\2\2\u01f7\u01fa\3\2\2\2\u01f8\u01f6\3\2\2\2\u01f9\u01f1\3\2\2\2\u01f9"+
		"\u01fa\3\2\2\2\u01fa\u01fb\3\2\2\2\u01fb\u01fc\7\24\2\2\u01fc?\3\2\2\2"+
		"\u01fd\u01ff\5D#\2\u01fe\u0200\5L\'\2\u01ff\u01fe\3\2\2\2\u01ff\u0200"+
		"\3\2\2\2\u0200A\3\2\2\2\u0201\u0204\5D#\2\u0202\u0205\5L\'\2\u0203\u0205"+
		"\7q\2\2\u0204\u0202\3\2\2\2\u0204\u0203\3\2\2\2\u0204\u0205\3\2\2\2\u0205"+
		"\u0206\3\2\2\2\u0206\u0207\5\u00b2Z\2\u0207C\3\2\2\2\u0208\u0209\b#\1"+
		"\2\u0209\u020e\5v<\2\u020a\u020e\5F$\2\u020b\u020e\5H%\2\u020c\u020e\5"+
		"J&\2\u020d\u0208\3\2\2\2\u020d\u020a\3\2\2\2\u020d\u020b\3\2\2\2\u020d"+
		"\u020c\3\2\2\2\u020e\u0217\3\2\2\2\u020f\u0210\f\4\2\2\u0210\u0212\7%"+
		"\2\2\u0211\u0213\5x=\2\u0212\u0211\3\2\2\2\u0212\u0213\3\2\2\2\u0213\u0214"+
		"\3\2\2\2\u0214\u0216\7&\2\2\u0215\u020f\3\2\2\2\u0216\u0219\3\2\2\2\u0217"+
		"\u0215\3\2\2\2\u0217\u0218\3\2\2\2\u0218E\3\2\2\2\u0219\u0217\3\2\2\2"+
		"\u021a\u021f\5\u00b2Z\2\u021b\u021c\7\'\2\2\u021c\u021e\5\u00b2Z\2\u021d"+
		"\u021b\3\2\2\2\u021e\u0221\3\2\2\2\u021f\u021d\3\2\2\2\u021f\u0220\3\2"+
		"\2\2\u0220G\3\2\2\2\u0221\u021f\3\2\2\2\u0222\u0223\7(\2\2\u0223\u0224"+
		"\7\23\2\2\u0224\u0225\5v<\2\u0225\u0226\7)\2\2\u0226\u0227\5D#\2\u0227"+
		"\u0228\7\24\2\2\u0228I\3\2\2\2\u0229\u022a\7\32\2\2\u022a\u0230\5> \2"+
		"\u022b\u022f\7x\2\2\u022c\u022f\7t\2\2\u022d\u022f\5N(\2\u022e\u022b\3"+
		"\2\2\2\u022e\u022c\3\2\2\2\u022e\u022d\3\2\2\2\u022f\u0232\3\2\2\2\u0230"+
		"\u022e\3\2\2\2\u0230\u0231\3\2\2\2\u0231\u0235\3\2\2\2\u0232\u0230\3\2"+
		"\2\2\u0233\u0234\7\33\2\2\u0234\u0236\5> \2\u0235\u0233\3\2\2\2\u0235"+
		"\u0236\3\2\2\2\u0236K\3\2\2\2\u0237\u0238\t\6\2\2\u0238M\3\2\2\2\u0239"+
		"\u023a\t\7\2\2\u023aO\3\2\2\2\u023b\u023f\7\17\2\2\u023c\u023e\5T+\2\u023d"+
		"\u023c\3\2\2\2\u023e\u0241\3\2\2\2\u023f\u023d\3\2\2\2\u023f\u0240\3\2"+
		"\2\2\u0240\u0242\3\2\2\2\u0241\u023f\3\2\2\2\u0242\u0243\7\21\2\2\u0243"+
		"Q\3\2\2\2\u0244\u0245\7-\2\2\u0245\u0246\5P)\2\u0246S\3\2\2\2\u0247\u0256"+
		"\5Z.\2\u0248\u0256\5\\/\2\u0249\u0256\5`\61\2\u024a\u0256\5P)\2\u024b"+
		"\u0256\5R*\2\u024c\u0256\5b\62\2\u024d\u0256\5d\63\2\u024e\u0256\5f\64"+
		"\2\u024f\u0256\5h\65\2\u0250\u0256\5j\66\2\u0251\u0256\5l\67\2\u0252\u0256"+
		"\5n8\2\u0253\u0256\5V,\2\u0254\u0256\5^\60\2\u0255\u0247\3\2\2\2\u0255"+
		"\u0248\3\2\2\2\u0255\u0249\3\2\2\2\u0255\u024a\3\2\2\2\u0255\u024b\3\2"+
		"\2\2\u0255\u024c\3\2\2\2\u0255\u024d\3\2\2\2\u0255\u024e\3\2\2\2\u0255"+
		"\u024f\3\2\2\2\u0255\u0250\3\2\2\2\u0255\u0251\3\2\2\2\u0255\u0252\3\2"+
		"\2\2\u0255\u0253\3\2\2\2\u0255\u0254\3\2\2\2\u0256U\3\2\2\2\u0257\u0258"+
		"\7.\2\2\u0258W\3\2\2\2\u0259\u025a\5x=\2\u025a\u025b\7\4\2\2\u025bY\3"+
		"\2\2\2\u025c\u025d\7/\2\2\u025d\u025e\7\23\2\2\u025e\u025f\5x=\2\u025f"+
		"\u0260\7\24\2\2\u0260\u0263\5T+\2\u0261\u0262\7\60\2\2\u0262\u0264\5T"+
		"+\2\u0263\u0261\3\2\2\2\u0263\u0264\3\2\2\2\u0264[\3\2\2\2\u0265\u0266"+
		"\7\61\2\2\u0266\u0267\7\23\2\2\u0267\u0268\5x=\2\u0268\u0269\7\24\2\2"+
		"\u0269\u026a\5T+\2\u026a]\3\2\2\2\u026b\u026e\5p9\2\u026c\u026e\5X-\2"+
		"\u026d\u026b\3\2\2\2\u026d\u026c\3\2\2\2\u026e_\3\2\2\2\u026f\u0270\7"+
		"\26\2\2\u0270\u0273\7\23\2\2\u0271\u0274\5^\60\2\u0272\u0274\7\4\2\2\u0273"+
		"\u0271\3\2\2\2\u0273\u0272\3\2\2\2\u0274\u0276\3\2\2\2\u0275\u0277\5x"+
		"=\2\u0276\u0275\3\2\2\2\u0276\u0277\3\2\2\2\u0277\u0278\3\2\2\2\u0278"+
		"\u027a\7\4\2\2\u0279\u027b\5x=\2\u027a\u0279\3\2\2\2\u027a\u027b\3\2\2"+
		"\2\u027b\u027c\3\2\2\2\u027c\u027d\7\24\2\2\u027d\u027e\5T+\2\u027ea\3"+
		"\2\2\2\u027f\u0281\7\62\2\2\u0280\u0282\7\u0082\2\2\u0281\u0280\3\2\2"+
		"\2\u0281\u0282\3\2\2\2\u0282\u0283\3\2\2\2\u0283\u0284\5\u0088E\2\u0284"+
		"c\3\2\2\2\u0285\u0286\7\63\2\2\u0286\u0287\5T+\2\u0287\u0288\7\61\2\2"+
		"\u0288\u0289\7\23\2\2\u0289\u028a\5x=\2\u028a\u028b\7\24\2\2\u028b\u028c"+
		"\7\4\2\2\u028ce\3\2\2\2\u028d\u028e\7r\2\2\u028e\u028f\7\4\2\2\u028fg"+
		"\3\2\2\2\u0290\u0291\7p\2\2\u0291\u0292\7\4\2\2\u0292i\3\2\2\2\u0293\u0295"+
		"\7\64\2\2\u0294\u0296\5x=\2\u0295\u0294\3\2\2\2\u0295\u0296\3\2\2\2\u0296"+
		"\u0297\3\2\2\2\u0297\u0298\7\4\2\2\u0298k\3\2\2\2\u0299\u029a\7\65\2\2"+
		"\u029a\u029b\7\4\2\2\u029bm\3\2\2\2\u029c\u029d\7\66\2\2\u029d\u029e\5"+
		"\u0086D\2\u029e\u029f\7\4\2\2\u029fo\3\2\2\2\u02a0\u02a1\7\67\2\2\u02a1"+
		"\u02a8\5t;\2\u02a2\u02a8\5B\"\2\u02a3\u02a4\7\23\2\2\u02a4\u02a5\5r:\2"+
		"\u02a5\u02a6\7\24\2\2\u02a6\u02a8\3\2\2\2\u02a7\u02a0\3\2\2\2\u02a7\u02a2"+
		"\3\2\2\2\u02a7\u02a3\3\2\2\2\u02a8\u02ab\3\2\2\2\u02a9\u02aa\7\13\2\2"+
		"\u02aa\u02ac\5x=\2\u02ab\u02a9\3\2\2\2\u02ab\u02ac\3\2\2\2\u02ac\u02ad"+
		"\3\2\2\2\u02ad\u02ae\7\4\2\2\u02aeq\3\2\2\2\u02af\u02b1\5B\"\2\u02b0\u02af"+
		"\3\2\2\2\u02b0\u02b1\3\2\2\2\u02b1\u02b8\3\2\2\2\u02b2\u02b4\7\20\2\2"+
		"\u02b3\u02b5\5B\"\2\u02b4\u02b3\3\2\2\2\u02b4\u02b5\3\2\2\2\u02b5\u02b7"+
		"\3\2\2\2\u02b6\u02b2\3\2\2\2\u02b7\u02ba\3\2\2\2\u02b8\u02b6\3\2\2\2\u02b8"+
		"\u02b9\3\2\2\2\u02b9s\3\2\2\2\u02ba\u02b8\3\2\2\2\u02bb\u02c2\7\23\2\2"+
		"\u02bc\u02be\5\u00b2Z\2\u02bd\u02bc\3\2\2\2\u02bd\u02be\3\2\2\2\u02be"+
		"\u02bf\3\2\2\2\u02bf\u02c1\7\20\2\2\u02c0\u02bd\3\2\2\2\u02c1\u02c4\3"+
		"\2\2\2\u02c2\u02c0\3\2\2\2\u02c2\u02c3\3\2\2\2\u02c3\u02c6\3\2\2\2\u02c4"+
		"\u02c2\3\2\2\2\u02c5\u02c7\5\u00b2Z\2\u02c6\u02c5\3\2\2\2\u02c6\u02c7"+
		"\3\2\2\2\u02c7\u02c8\3\2\2\2\u02c8\u02c9\7\24\2\2\u02c9u\3\2\2\2\u02ca"+
		"\u02cb\t\b\2\2\u02cbw\3\2\2\2\u02cc\u02cd\b=\1\2\u02cd\u02ce\7=\2\2\u02ce"+
		"\u0305\5D#\2\u02cf\u02d0\7\23\2\2\u02d0\u02d1\5x=\2\u02d1\u02d2\7\24\2"+
		"\2\u02d2\u0305\3\2\2\2\u02d3\u02d4\t\t\2\2\u02d4\u0305\5x= \u02d5\u02d6"+
		"\t\n\2\2\u02d6\u0305\5x=\37\u02d7\u02d8\t\13\2\2\u02d8\u0305\5x=\36\u02d9"+
		"\u02da\7\u0090\2\2\u02da\u0305\5x=\35\u02db\u02dc\7\6\2\2\u02dc\u0305"+
		"\5x=\34\u02dd\u0305\5z>\2\u02de\u0305\5|?\2\u02df\u02e0\7\23\2\2\u02e0"+
		"\u02e1\7R\2\2\u02e1\u02e2\5D#\2\u02e2\u02e3\7\u0081\2\2\u02e3\u02e4\7"+
		"\4\2\2\u02e4\u02e5\5x=\2\u02e5\u02e6\7\24\2\2\u02e6\u0305\3\2\2\2\u02e7"+
		"\u02e8\7\23\2\2\u02e8\u02e9\7S\2\2\u02e9\u02ea\5D#\2\u02ea\u02eb\7\u0081"+
		"\2\2\u02eb\u02ec\7\4\2\2\u02ec\u02ed\5x=\2\u02ed\u02ee\7\24\2\2\u02ee"+
		"\u0305\3\2\2\2\u02ef\u02f0\7T\2\2\u02f0\u02f1\7\23\2\2\u02f1\u02f2\5x"+
		"=\2\u02f2\u02f3\7\24\2\2\u02f3\u0305\3\2\2\2\u02f4\u02f5\7U\2\2\u02f5"+
		"\u02f6\7\23\2\2\u02f6\u02f7\5x=\2\u02f7\u02f8\7\24\2\2\u02f8\u0305\3\2"+
		"\2\2\u02f9\u02fa\7V\2\2\u02fa\u02fb\7\23\2\2\u02fb\u02fc\5x=\2\u02fc\u02fd"+
		"\7\24\2\2\u02fd\u0305\3\2\2\2\u02fe\u02ff\7W\2\2\u02ff\u0300\7\23\2\2"+
		"\u0300\u0301\5x=\2\u0301\u0302\7\24\2\2\u0302\u0305\3\2\2\2\u0303\u0305"+
		"\7X\2\2\u0304\u02cc\3\2\2\2\u0304\u02cf\3\2\2\2\u0304\u02d3\3\2\2\2\u0304"+
		"\u02d5\3\2\2\2\u0304\u02d7\3\2\2\2\u0304\u02d9\3\2\2\2\u0304\u02db\3\2"+
		"\2\2\u0304\u02dd\3\2\2\2\u0304\u02de\3\2\2\2\u0304\u02df\3\2\2\2\u0304"+
		"\u02e7\3\2\2\2\u0304\u02ef\3\2\2\2\u0304\u02f4\3\2\2\2\u0304\u02f9\3\2"+
		"\2\2\u0304\u02fe\3\2\2\2\u0304\u0303\3\2\2\2\u0305\u034a\3\2\2\2\u0306"+
		"\u0307\f\33\2\2\u0307\u0308\7@\2\2\u0308\u0349\5x=\34\u0309\u030a\f\32"+
		"\2\2\u030a\u030b\t\f\2\2\u030b\u0349\5x=\33\u030c\u030d\f\31\2\2\u030d"+
		"\u030e\t\n\2\2\u030e\u0349\5x=\32\u030f\u0310\f\30\2\2\u0310\u0311\t\r"+
		"\2\2\u0311\u0349\5x=\31\u0312\u0313\f\27\2\2\u0313\u0314\7\u008e\2\2\u0314"+
		"\u0349\5x=\30\u0315\u0316\f\26\2\2\u0316\u0317\7\5\2\2\u0317\u0349\5x"+
		"=\27\u0318\u0319\f\25\2\2\u0319\u031a\7\u008f\2\2\u031a\u0349\5x=\26\u031b"+
		"\u031c\f\24\2\2\u031c\u031d\t\16\2\2\u031d\u0349\5x=\25\u031e\u031f\f"+
		"\23\2\2\u031f\u0320\t\17\2\2\u0320\u0349\5x=\24\u0321\u0322\f\22\2\2\u0322"+
		"\u0323\7\u008a\2\2\u0323\u0349\5x=\23\u0324\u0325\f\21\2\2\u0325\u0326"+
		"\7\u008b\2\2\u0326\u0349\5x=\22\u0327\u0328\f\20\2\2\u0328\u0329\7C\2"+
		"\2\u0329\u032a\5x=\2\u032a\u032b\7D\2\2\u032b\u032c\5x=\21\u032c\u0349"+
		"\3\2\2\2\u032d\u032e\f\17\2\2\u032e\u032f\t\20\2\2\u032f\u0349\5x=\20"+
		"\u0330\u0331\f\r\2\2\u0331\u0332\7O\2\2\u0332\u0349\5x=\16\u0333\u0334"+
		"\f\f\2\2\u0334\u0335\7P\2\2\u0335\u0349\5x=\r\u0336\u0337\f\13\2\2\u0337"+
		"\u0338\7Q\2\2\u0338\u0349\5x=\f\u0339\u033a\f&\2\2\u033a\u0349\t\t\2\2"+
		"\u033b\u033c\f$\2\2\u033c\u033d\7%\2\2\u033d\u033e\5x=\2\u033e\u033f\7"+
		"&\2\2\u033f\u0349\3\2\2\2\u0340\u0341\f#\2\2\u0341\u0342\7\23\2\2\u0342"+
		"\u0343\5\u0084C\2\u0343\u0344\7\24\2\2\u0344\u0349\3\2\2\2\u0345\u0346"+
		"\f\"\2\2\u0346\u0347\7\'\2\2\u0347\u0349\5\u00b2Z\2\u0348\u0306\3\2\2"+
		"\2\u0348\u0309\3\2\2\2\u0348\u030c\3\2\2\2\u0348\u030f\3\2\2\2\u0348\u0312"+
		"\3\2\2\2\u0348\u0315\3\2\2\2\u0348\u0318\3\2\2\2\u0348\u031b\3\2\2\2\u0348"+
		"\u031e\3\2\2\2\u0348\u0321\3\2\2\2\u0348\u0324\3\2\2\2\u0348\u0327\3\2"+
		"\2\2\u0348\u032d\3\2\2\2\u0348\u0330\3\2\2\2\u0348\u0333\3\2\2\2\u0348"+
		"\u0336\3\2\2\2\u0348\u0339\3\2\2\2\u0348\u033b\3\2\2\2\u0348\u0340\3\2"+
		"\2\2\u0348\u0345\3\2\2\2\u0349\u034c\3\2\2\2\u034a\u0348\3\2\2\2\u034a"+
		"\u034b\3\2\2\2\u034by\3\2\2\2\u034c\u034a\3\2\2\2\u034d\u0355\7h\2\2\u034e"+
		"\u0355\5\u00b0Y\2\u034f\u0355\7l\2\2\u0350\u0355\7\u0082\2\2\u0351\u0355"+
		"\5\u00b2Z\2\u0352\u0355\5\u00acW\2\u0353\u0355\5\u00aeX\2\u0354\u034d"+
		"\3\2\2\2\u0354\u034e\3\2\2\2\u0354\u034f\3\2\2\2\u0354\u0350\3\2\2\2\u0354"+
		"\u0351\3\2\2\2\u0354\u0352\3\2\2\2\u0354\u0353\3\2\2\2\u0355{\3\2\2\2"+
		"\u0356\u0357\7Y\2\2\u0357\u0358\7\23\2\2\u0358\u0359\5D#\2\u0359\u035a"+
		"\7\24\2\2\u035a\u035b\7\'\2\2\u035b\u035c\t\21\2\2\u035c}\3\2\2\2\u035d"+
		"\u0362\5x=\2\u035e\u035f\7\20\2\2\u035f\u0361\5x=\2\u0360\u035e\3\2\2"+
		"\2\u0361\u0364\3\2\2\2\u0362\u0360\3\2\2\2\u0362\u0363\3\2\2\2\u0363\177"+
		"\3\2\2\2\u0364\u0362\3\2\2\2\u0365\u036a\5\u0082B\2\u0366\u0367\7\20\2"+
		"\2\u0367\u0369\5\u0082B\2\u0368\u0366\3\2\2\2\u0369\u036c\3\2\2\2\u036a"+
		"\u0368\3\2\2\2\u036a\u036b\3\2\2\2\u036b\u036e\3\2\2\2\u036c\u036a\3\2"+
		"\2\2\u036d\u036f\7\20\2\2\u036e\u036d\3\2\2\2\u036e\u036f\3\2\2\2\u036f"+
		"\u0081\3\2\2\2\u0370\u0371\5\u00b2Z\2\u0371\u0372\7D\2\2\u0372\u0373\5"+
		"x=\2\u0373\u0083\3\2\2\2\u0374\u0376\7\17\2\2\u0375\u0377\5\u0080A\2\u0376"+
		"\u0375\3\2\2\2\u0376\u0377\3\2\2\2\u0377\u0378\3\2\2\2\u0378\u037d\7\21"+
		"\2\2\u0379\u037b\5~@\2\u037a\u0379\3\2\2\2\u037a\u037b\3\2\2\2\u037b\u037d"+
		"\3\2\2\2\u037c\u0374\3\2\2\2\u037c\u037a\3\2\2\2\u037d\u0085\3\2\2\2\u037e"+
		"\u037f\5x=\2\u037f\u0380\7\23\2\2\u0380\u0381\5\u0084C\2\u0381\u0382\7"+
		"\24\2\2\u0382\u0087\3\2\2\2\u0383\u0387\7\17\2\2\u0384\u0386\5\u008aF"+
		"\2\u0385\u0384\3\2\2\2\u0386\u0389\3\2\2\2\u0387\u0385\3\2\2\2\u0387\u0388"+
		"\3\2\2\2\u0388\u038a\3\2\2\2\u0389\u0387\3\2\2\2\u038a\u038b\7\21\2\2"+
		"\u038b\u0089\3\2\2\2\u038c\u039e\5\u00b2Z\2\u038d\u039e\5\u0088E\2\u038e"+
		"\u039e\5\u008cG\2\u038f\u039e\5\u0090I\2\u0390\u039e\5\u0092J\2\u0391"+
		"\u039e\5\u0098M\2\u0392\u039e\5\u009aN\2\u0393\u039e\5\u009cO\2\u0394"+
		"\u039e\5\u00a0Q\2\u0395\u039e\5\u00a4S\2\u0396\u039e\5\u00a6T\2\u0397"+
		"\u039e\7p\2\2\u0398\u039e\7r\2\2\u0399\u039e\5\u00aaV\2\u039a\u039e\5"+
		"\u00b0Y\2\u039b\u039e\7\u0082\2\2\u039c\u039e\7l\2\2\u039d\u038c\3\2\2"+
		"\2\u039d\u038d\3\2\2\2\u039d\u038e\3\2\2\2\u039d\u038f\3\2\2\2\u039d\u0390"+
		"\3\2\2\2\u039d\u0391\3\2\2\2\u039d\u0392\3\2\2\2\u039d\u0393\3\2\2\2\u039d"+
		"\u0394\3\2\2\2\u039d\u0395\3\2\2\2\u039d\u0396\3\2\2\2\u039d\u0397\3\2"+
		"\2\2\u039d\u0398\3\2\2\2\u039d\u0399\3\2\2\2\u039d\u039a\3\2\2\2\u039d"+
		"\u039b\3\2\2\2\u039d\u039c\3\2\2\2\u039e\u008b\3\2\2\2\u039f\u03a2\5\u008e"+
		"H\2\u03a0\u03a2\5\u00a8U\2\u03a1\u039f\3\2\2\2\u03a1\u03a0\3\2\2\2\u03a2"+
		"\u008d\3\2\2\2\u03a3\u03a8\7\64\2\2\u03a4\u03a8\78\2\2\u03a5\u03a8\7<"+
		"\2\2\u03a6\u03a8\5\u00b2Z\2\u03a7\u03a3\3\2\2\2\u03a7\u03a4\3\2\2\2\u03a7"+
		"\u03a5\3\2\2\2\u03a7\u03a6\3\2\2\2\u03a8\u03b5\3\2\2\2\u03a9\u03ab\7\23"+
		"\2\2\u03aa\u03ac\5\u008cG\2\u03ab\u03aa\3\2\2\2\u03ab\u03ac\3\2\2\2\u03ac"+
		"\u03b1\3\2\2\2\u03ad\u03ae\7\20\2\2\u03ae\u03b0\5\u008cG\2\u03af\u03ad"+
		"\3\2\2\2\u03b0\u03b3\3\2\2\2\u03b1\u03af\3\2\2\2\u03b1\u03b2\3\2\2\2\u03b2"+
		"\u03b4\3\2\2\2\u03b3\u03b1\3\2\2\2\u03b4\u03b6\7\24\2\2\u03b5\u03a9\3"+
		"\2\2\2\u03b5\u03b6\3\2\2\2\u03b6\u008f\3\2\2\2\u03b7\u03b8\7\\\2\2\u03b8"+
		"\u03bb\5\u0094K\2\u03b9\u03ba\7]\2\2\u03ba\u03bc\5\u008cG\2\u03bb\u03b9"+
		"\3\2\2\2\u03bb\u03bc\3\2\2\2\u03bc\u0091\3\2\2\2\u03bd\u03be\5\u0094K"+
		"\2\u03be\u03bf\7]\2\2\u03bf\u03c0\5\u008cG\2\u03c0\u0093\3\2\2\2\u03c1"+
		"\u03c7\5\u00b2Z\2\u03c2\u03c3\7\23\2\2\u03c3\u03c4\5\u0096L\2\u03c4\u03c5"+
		"\7\24\2\2\u03c5\u03c7\3\2\2\2\u03c6\u03c1\3\2\2\2\u03c6\u03c2\3\2\2\2"+
		"\u03c7\u0095\3\2\2\2\u03c8\u03cd\5\u00b2Z\2\u03c9\u03ca\7\20\2\2\u03ca"+
		"\u03cc\5\u00b2Z\2\u03cb\u03c9\3\2\2\2\u03cc\u03cf\3\2\2\2\u03cd\u03cb"+
		"\3\2\2\2\u03cd\u03ce\3\2\2\2\u03ce\u0097\3\2\2\2\u03cf\u03cd\3\2\2\2\u03d0"+
		"\u03d1\7^\2\2\u03d1\u03d2\5\u00b2Z\2\u03d2\u0099\3\2\2\2\u03d3\u03d4\5"+
		"\u00b2Z\2\u03d4\u03d5\7D\2\2\u03d5\u009b\3\2\2\2\u03d6\u03d7\7_\2\2\u03d7"+
		"\u03db\5\u008cG\2\u03d8\u03da\5\u009eP\2\u03d9\u03d8\3\2\2\2\u03da\u03dd"+
		"\3\2\2\2\u03db\u03d9\3\2\2\2\u03db\u03dc\3\2\2\2\u03dc\u009d\3\2\2\2\u03dd"+
		"\u03db\3\2\2\2\u03de\u03df\7`\2\2\u03df\u03e0\5\u00a8U\2\u03e0\u03e1\5"+
		"\u0088E\2\u03e1\u03e5\3\2\2\2\u03e2\u03e3\7a\2\2\u03e3\u03e5\5\u0088E"+
		"\2\u03e4\u03de\3\2\2\2\u03e4\u03e2\3\2\2\2\u03e5\u009f\3\2\2\2\u03e6\u03e7"+
		"\7\32\2\2\u03e7\u03e8\5\u00b2Z\2\u03e8\u03ea\7\23\2\2\u03e9\u03eb\5\u0096"+
		"L\2\u03ea\u03e9\3\2\2\2\u03ea\u03eb\3\2\2\2\u03eb\u03ec\3\2\2\2\u03ec"+
		"\u03ee\7\24\2\2\u03ed\u03ef\5\u00a2R\2\u03ee\u03ed\3\2\2\2\u03ee\u03ef"+
		"\3\2\2\2\u03ef\u03f0\3\2\2\2\u03f0\u03f1\5\u0088E\2\u03f1\u00a1\3\2\2"+
		"\2\u03f2\u03f3\7O\2\2\u03f3\u03f4\5\u0096L\2\u03f4\u00a3\3\2\2\2\u03f5"+
		"\u03f8\7\26\2\2\u03f6\u03f9\5\u0088E\2\u03f7\u03f9\5\u008cG\2\u03f8\u03f6"+
		"\3\2\2\2\u03f8\u03f7\3\2\2\2\u03f9\u03fa\3\2\2\2\u03fa\u03fd\5\u008cG"+
		"\2\u03fb\u03fe\5\u0088E\2\u03fc\u03fe\5\u008cG\2\u03fd\u03fb\3\2\2\2\u03fd"+
		"\u03fc\3\2\2\2\u03fe\u03ff\3\2\2\2\u03ff\u0400\5\u0088E\2\u0400\u00a5"+
		"\3\2\2\2\u0401\u0402\7/\2\2\u0402\u0403\5\u008cG\2\u0403\u0404\5\u0088"+
		"E\2\u0404\u00a7\3\2\2\2\u0405\u0406\t\22\2\2\u0406\u00a9\3\2\2\2\u0407"+
		"\u0408\7\62\2\2\u0408\u0409\5\u00b2Z\2\u0409\u040a\5\u0088E\2\u040a\u00ab"+
		"\3\2\2\2\u040b\u040d\7\23\2\2\u040c\u040e\5x=\2\u040d\u040c\3\2\2\2\u040d"+
		"\u040e\3\2\2\2\u040e\u0415\3\2\2\2\u040f\u0411\7\20\2\2\u0410\u0412\5"+
		"x=\2\u0411\u0410\3\2\2\2\u0411\u0412\3\2\2\2\u0412\u0414\3\2\2\2\u0413"+
		"\u040f\3\2\2\2\u0414\u0417\3\2\2\2\u0415\u0413\3\2\2\2\u0415\u0416\3\2"+
		"\2\2\u0416\u0418\3\2\2\2\u0417\u0415\3\2\2\2\u0418\u0426\7\24\2\2\u0419"+
		"\u0422\7%\2\2\u041a\u041f\5x=\2\u041b\u041c\7\20\2\2\u041c\u041e\5x=\2"+
		"\u041d\u041b\3\2\2\2\u041e\u0421\3\2\2\2\u041f\u041d\3\2\2\2\u041f\u0420"+
		"\3\2\2\2\u0420\u0423\3\2\2\2\u0421\u041f\3\2\2\2\u0422\u041a\3\2\2\2\u0422"+
		"\u0423\3\2\2\2\u0423\u0424\3\2\2\2\u0424\u0426\7&\2\2\u0425\u040b\3\2"+
		"\2\2\u0425\u0419\3\2\2\2\u0426\u00ad\3\2\2\2\u0427\u0428\5v<\2\u0428\u00af"+
		"\3\2\2\2\u0429\u042b\t\23\2\2\u042a\u042c\7k\2\2\u042b\u042a\3\2\2\2\u042b"+
		"\u042c\3\2\2\2\u042c\u00b1\3\2\2\2\u042d\u042e\t\24\2\2\u042e\u00b3\3"+
		"\2\2\2m\u00b8\u00ba\u00c8\u00cc\u00d1\u00d8\u00de\u00e4\u00e8\u00f4\u00fc"+
		"\u00ff\u0109\u010c\u0112\u011e\u0123\u012d\u0133\u0139\u0142\u0150\u0153"+
		"\u015f\u0162\u0169\u016c\u0170\u0175\u0179\u0186\u0188\u018f\u0199\u019f"+
		"\u01a7\u01be\u01c6\u01ce\u01d1\u01d7\u01da\u01e2\u01e5\u01eb\u01ee\u01f6"+
		"\u01f9\u01ff\u0204\u020d\u0212\u0217\u021f\u022e\u0230\u0235\u023f\u0255"+
		"\u0263\u026d\u0273\u0276\u027a\u0281\u0295\u02a7\u02ab\u02b0\u02b4\u02b8"+
		"\u02bd\u02c2\u02c6\u0304\u0348\u034a\u0354\u0362\u036a\u036e\u0376\u037a"+
		"\u037c\u0387\u039d\u03a1\u03a7\u03ab\u03b1\u03b5\u03bb\u03c6\u03cd\u03db"+
		"\u03e4\u03ea\u03ee\u03f8\u03fd\u040d\u0411\u0415\u041f\u0422\u0425\u042b";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}