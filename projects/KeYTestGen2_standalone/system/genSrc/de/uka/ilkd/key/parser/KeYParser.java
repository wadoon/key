// $ANTLR 2.7.7 (2006-11-01): "keyparser.g" -> "KeYParser.java"$


  package de.uka.ilkd.key.parser;

  import antlr.*;

  import java.io.*;
  import java.util.*;
  import java.math.BigInteger;

  import de.uka.ilkd.key.collection.*;
  import de.uka.ilkd.key.logic.*;
  import de.uka.ilkd.key.logic.op.*;
  import de.uka.ilkd.key.logic.sort.*;

  import de.uka.ilkd.key.proof.*;
  import de.uka.ilkd.key.proof.init.*;
  import de.uka.ilkd.key.proof.io.*;

  import de.uka.ilkd.key.rule.*;
  import de.uka.ilkd.key.rule.tacletbuilder.*;
  import de.uka.ilkd.key.rule.conditions.*;
 
  import de.uka.ilkd.key.speclang.*;

  import de.uka.ilkd.key.speclang.dl.translation.DLSpecFactory;

  import de.uka.ilkd.key.util.*;

  import de.uka.ilkd.key.java.JavaInfo;
  import de.uka.ilkd.key.java.Services;
  import de.uka.ilkd.key.java.JavaReader;
  import de.uka.ilkd.key.java.SchemaJavaReader;
  import de.uka.ilkd.key.java.abstraction.*;
  import de.uka.ilkd.key.java.visitor.*;
  import de.uka.ilkd.key.java.Recoder2KeY;
  import de.uka.ilkd.key.java.SchemaRecoder2KeY;
  import de.uka.ilkd.key.java.StatementBlock;
  import de.uka.ilkd.key.java.declaration.VariableDeclaration;
  import de.uka.ilkd.key.java.recoderext.*;
  import de.uka.ilkd.key.java.recoderext.adt.*;
  import de.uka.ilkd.key.pp.AbbrevMap;
  import de.uka.ilkd.key.pp.LogicPrinter;

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

/** 
 * General KeY parser, can work in different modes (parserMode)
 */
public class KeYParser extends antlr.LLkParser       implements KeYParserTokenTypes
 {

    private static final TermFactory tf = TermFactory.DEFAULT;

    private static final Sort[] AN_ARRAY_OF_SORTS = new Sort[0];
    private static final Term[] AN_ARRAY_OF_TERMS = new Term[0];

    private static final int NORMAL_NONRIGID = 0;
    private static final int LOCATION_MODIFIER = 1;

    static HashMap<String, Character> prooflabel2tag = new HashMap<String, Character>(15);
    static {
      prooflabel2tag.put("branch", new Character('b'));
      prooflabel2tag.put("rule", new Character('r'));
      prooflabel2tag.put("term", new Character('t'));
      prooflabel2tag.put("formula", new Character('f'));
      prooflabel2tag.put("inst", new Character('i'));
      prooflabel2tag.put("ifseqformula", new Character('q'));
      prooflabel2tag.put("ifdirectformula", new Character('d'));
      prooflabel2tag.put("heur", new Character('h'));
      prooflabel2tag.put("builtin", new Character('n'));
      prooflabel2tag.put("keyLog", new Character('l'));
      prooflabel2tag.put("keyUser", new Character('u'));
      prooflabel2tag.put("keyVersion", new Character('v'));
      prooflabel2tag.put("keySettings", new Character('s'));
      prooflabel2tag.put("contract", new Character('c'));
      prooflabel2tag.put("ifInst", new Character('x'));		
      prooflabel2tag.put("userinteraction", new Character('a'));
      prooflabel2tag.put("newnames", new Character('w'));
      prooflabel2tag.put("autoModeTime", new Character('e'));
   }

    private NamespaceSet nss;
    private HashMap<String, String> category2Default = new HashMap<String, String>();
    private boolean onlyWith=false;
    private ImmutableSet<Choice> activatedChoices = DefaultImmutableSet.<Choice>nil();
    private HashSet usedChoiceCategories = new HashSet();
    private HashMap taclet2Builder;
    private AbbrevMap scm;
    private KeYExceptionHandler keh = null;

    // these variables are set if a file is read in step by
    // step. This used when reading in LDTs because of cyclic
    // dependencies.
    private boolean skip_schemavariables;
    private boolean skip_functions;
    private boolean skip_predicates;
    private boolean skip_sorts;
    private boolean skip_rulesets;
    private boolean skip_taclets;
    private boolean parse_includes = false;
    private Includes includes = new Includes();

    private boolean schemaMode = false;
    private ParserMode parserMode;

    private String chooseContract = null;
    private String proofObligation = null;
    
    private int savedGuessing = -1;

    private int lineOffset=0;
    private int colOffset=0;
    private int stringLiteralLine=0; // HACK!

    private Services services;
    private JavaReader javaReader;

    // if this is used then we can capture parts of the input for later use
    private DeclPicker capturer = null;
    private IProgramMethod pm = null;

    private ImmutableSet<Taclet> taclets = DefaultImmutableSet.<Taclet>nil(); 
    private ImmutableSet<Contract> contracts = DefaultImmutableSet.<Contract>nil();
    private ImmutableSet<ClassInvariant> invs = DefaultImmutableSet.<ClassInvariant>nil();

    private ParserConfig schemaConfig;
    private ParserConfig normalConfig;
    
    // the current active config
    private ParserConfig parserConfig;

    private Term quantifiedArrayGuard = null;
    
    private TokenStreamSelector selector;

    /**
     * Although the parser mode can be deduced from the particular constructor
     * used we still require the caller to provide the parser mode explicitly, 
     * so that the code is readable.
     */
    public KeYParser(ParserMode mode, TokenStream lexer) {
	this((lexer instanceof KeYLexer)? ((KeYLexer)lexer).getSelector() : ((DeclPicker)lexer).getSelector(), 2);
        this.selector = (lexer instanceof KeYLexer)? ((KeYLexer)lexer).getSelector() : ((DeclPicker)lexer).getSelector();
	this.parserMode = mode;
	if(isTacletParser()) {
	    switchToSchemaMode();
	}
    }

    public KeYParser(ParserMode mode, TokenStream lexer, Services services) {
        this(mode, lexer);
        this.keh = services.getExceptionHandler();
    }

    /* Most general constructor, should only be used internally */
    private KeYParser(TokenStream lexer,
		     String filename,
                     Services services,
		     NamespaceSet nss,
		     ParserMode mode) {
        this(mode, lexer);
        setFilename(filename);
 	this.services = services;
	if(services != null)
          this.keh = services.getExceptionHandler();
	this.nss = nss;
        switchToNormalMode();
    }

    /** 
     * Used to construct Term parser - for first-order terms
     * and formulae.
     */  
    public KeYParser(ParserMode mode, 
                     TokenStream lexer,                   
                     String filename, 
                     JavaReader jr, 
                     Services services,
                     NamespaceSet nss, 
                     AbbrevMap scm) {
        this(lexer, filename, services, nss, mode);
        this.javaReader = jr;
        this.scm = scm;
    }

    public KeYParser(ParserMode mode, 
                     TokenStream lexer,
                     String filename,
                     Services services, 
                     NamespaceSet nss) {
        this(mode, 
             lexer, 
             filename,
             new SchemaRecoder2KeY(services, nss),
	     services, 
	     nss, 
	     new HashMap());
    }



    /** ONLY FOR TEST CASES.
     * Used to construct Global Declaration Term parser - for first-order 
     * terms and formulae. Variables in quantifiers are expected to be
     * declared globally in the variable namespace.  This parser is used
     * for test cases, where you want to know in advance which objects
     * will represent bound variables.
     */  
    public KeYParser(ParserMode mode, 
                     TokenStream lexer,
		     JavaReader jr,
		     NamespaceSet nss) {
        this(lexer, null, new Services(), nss, mode);
        this.scm = new AbbrevMap();
        this.javaReader = jr;
    }

    public KeYParser(ParserMode mode, 
                     TokenStream lexer,
		     Services services,
		     NamespaceSet nss) {
	this(mode, lexer, 
	     new Recoder2KeY(services,
		new KeYCrossReferenceServiceConfiguration(
		   services.getExceptionHandler()), 
		services.getJavaInfo().rec2key(), new NamespaceSet(), 
		services.getTypeConverter()),
   	     nss);
    }

    /**
     * Used to construct Taclet parser
     */  
    public KeYParser(ParserMode mode, 
                     TokenStream lexer,
                     String filename, 
                     SchemaJavaReader jr, 
                     Services services,  
                     NamespaceSet nss, 
                     HashMap taclet2Builder) {
        this(lexer, filename, services, nss, mode);
        switchToSchemaMode();
        this.scm = new AbbrevMap();
        this.javaReader = jr;
        this.taclet2Builder = taclet2Builder;
    }


    /** 
     * Used to construct Problem parser
     */  
    public KeYParser(ParserMode mode, 
    		     TokenStream lexer, 
                     String filename, 
                     ParserConfig schemaConfig,
                     ParserConfig normalConfig, 
                     HashMap taclet2Builder,
                     ImmutableSet<Taclet> taclets) { 
        this(lexer, filename, null, null, mode);
        if (lexer instanceof DeclPicker) {
            this.capturer = (DeclPicker) lexer;
        }
        if (normalConfig!=null)
        scm = new AbbrevMap();
        this.schemaConfig = schemaConfig;
        this.normalConfig = normalConfig;       
	switchToNormalMode();
        this.taclet2Builder = taclet2Builder;
        this.taclets = taclets;
        if(normalConfig != null){
            this.keh = normalConfig.services().getExceptionHandler();
        }else{
            this.keh = new KeYRecoderExcHandler();
        }
    }

    public KeYParser(ParserMode mode, TokenStream lexer, String filename) { 
        this(lexer, filename, null, null, mode);
        if (lexer instanceof DeclPicker) {
            this.capturer = (DeclPicker) lexer;
        }
        scm = new AbbrevMap();
        this.schemaConfig = null;
        this.normalConfig = null;       
	switchToNormalMode();
        this.taclet2Builder = null;
        this.taclets = null;
        this.keh = new KeYRecoderExcHandler();
    }


    /**
     * Parses taclet from string.
     */
    public static Taclet parseTaclet(String s, Services services) {
   	try {
	    KeYParser p =
                new KeYParser(ParserMode.TACLET,
                              new KeYLexer(new StringReader(s),null),
                              "No file. KeYParser.parseTaclet(\n" + s + ")\n",
                              services,
                              services.getNamespaces());
	    return p.taclet(DefaultImmutableSet.<Choice>nil());
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }

    public void recover( RecognitionException ex, BitSet tokenSet ) throws TokenStreamException {
     consume();
     consumeUntil( tokenSet );
    }

    public String getChooseContract() {
      return chooseContract;
    }
    
    public String getProofObligation() {
      return proofObligation;
    }
    
    public String getFilename() {
      return ((CharScanner)selector.getCurrentStream()).getFilename();
    }

    public void setFilename(String filename) {
      ((CharScanner)selector.getCurrentStream()).setFilename(filename);
    }
 
    private boolean isDeclParser() {
	return parserMode == ParserMode.DECLARATION;
    }

    private boolean isTermParser() {
	return parserMode == ParserMode.TERM;
    }

    private boolean isGlobalDeclTermParser() {
	return parserMode == ParserMode.GLOBALDECL;
    }

    private boolean isTacletParser() {
	return parserMode == ParserMode.TACLET;
    }

    private boolean isProblemParser() {
	return parserMode == ParserMode.PROBLEM;
    }

    public void reportError(RecognitionException ex){
        keh.reportException(ex);
    }

    public ImmutableSet<Choice> getActivatedChoices(){
        return activatedChoices;
    }
    
    public Includes getIncludes(){
        return includes;
    }

    public JavaInfo getJavaInfo() {
        if(isProblemParser()) 
          return parserConfig.javaInfo();
    	if(getServices() != null)
          return getServices().getJavaInfo();
	else
	  return null;
    }

    public Services getServices() {
        if(isProblemParser()) 
          return parserConfig.services();
        return services;
    }

    public NamespaceSet namespaces() {
        if(isProblemParser()) 
          return parserConfig.namespaces();
        return nss;
    }

    private Namespace sorts() {
        return namespaces().sorts();
    }

    private Namespace functions() {
        return namespaces().functions();
    }

    private Namespace ruleSets() {
        return namespaces().ruleSets();
    }

    private Namespace variables() {
        return namespaces().variables();
    }

    private Namespace programVariables() {
        return namespaces().programVariables();
    }

    private Namespace choices(){
        return namespaces().choices();
    }

    public ImmutableSet<Taclet> getTaclets(){
        return taclets;
    }

    public ImmutableSet<Contract> getContracts(){
        return contracts;
    }
    
    public ImmutableSet<ClassInvariant> getInvariants(){
    	return invs;
    }
    
    public HashMap<String, String> getCategory2Default(){
        return category2Default;
    }

    private boolean inSchemaMode() {
	if(isTermParser() && schemaMode)
	   Debug.fail("In Term parser mode schemaMode cannot be true.");
	if(isTacletParser() && !schemaMode)
	   Debug.fail("In Taclet parser mode schemaMode should always be true.");
        return schemaMode;
    }

    private void switchToSchemaMode() {
	if(!isTermParser()) {
          schemaMode = true;
	  if(isProblemParser())
            parserConfig = schemaConfig;    
	}
    }

    private void switchToNormalMode() {
	if(!isTermParser() && !isTacletParser()) {
          schemaMode = false;      
	  if(isProblemParser())
            parserConfig = normalConfig;
	}
    }

    private int getLine() {
        int line = -1;
        try {
            line = LT(0).getLine() + lineOffset;
        } catch (TokenStreamException e) {
            System.err.println("No further token in stream");
        }
        return line;
    }   

    private int getColumn() {
        int col = -1;
        try {
            col = LT(0).getColumn() + colOffset;
        } catch (TokenStreamException e) {
            System.err.println("No further token in stream");
        }
        return col;
    }   

    private void resetSkips() {
       skip_schemavariables = false;
       skip_functions       = false;
       skip_predicates      = false;
       skip_sorts           = false;
       skip_rulesets        = false;
       skip_taclets         = false;
    }

    private void skipFuncs() {
        skip_functions = true;
    }
    
    private void skipPreds() {
        skip_predicates = true;
    }

    private void skipTaclets() {
        skip_taclets = true;
    }

    private void skipVars() {
        skip_schemavariables = true;
    }

    private void skipSorts() {
        skip_sorts = true;
    }

    private void skipRuleSets() {
        skip_rulesets = true;
    }
    
    private Named lookup(Name n) {
       if(isProblemParser()) {
          final Namespace[] lookups = {
            schemaConfig.namespaces().programVariables(),
            normalConfig.namespaces().variables(), 
            schemaConfig.namespaces().variables(), 
            normalConfig.namespaces().functions(), 
            schemaConfig.namespaces().functions(), 
          };
          return doLookup(n,lookups);
       } else {
          final Namespace[] lookups = {
              programVariables(), variables(),
              functions()
          };
          return doLookup(n,lookups);
       }
    }

    private static Named doLookup(Name n, Namespace[] lookups) {
        for (int i = 0; i<lookups.length; i++) {
            if (lookups[i].lookup(n) != null) {
                return lookups[i].lookup(n);
            }
        }
        return null;    
    }

    private void addInclude(String filename, boolean relativePath, boolean ldt){
        RuleSource source=null;
        if (relativePath) {
            int end = getFilename().lastIndexOf(File.separator);
            int start = 0;
            filename = filename.replace('/', File.separatorChar);
            filename = filename.replace('\\', File.separatorChar);
            if(getFilename().startsWith("file:")){
                start = 5;
            }
            File path=new File(getFilename().substring(start,end+1)+filename);
            try{ 
                source = RuleSource.initRuleFile(path.toURL()); 
            }catch(java.net.MalformedURLException e){
                System.err.println("Exception due to malformed URL of file "+
                                   filename+"\n " +e);
            }
        } else {
            source = RuleSource.initRuleFile(filename+".key"); 
        }
        if (ldt) {
            includes.putLDT(filename, source);
        } else {
            includes.put(filename, source);
        }
    }  

    
    public void parseSorts() throws RecognitionException, 
    				    TokenStreamException {
      resetSkips(); 
      skipFuncs(); 
      skipPreds(); 
      skipRuleSets();
      skipVars();
      skipTaclets();
      decls();
      resetSkips();
    }    

    public void parseFunctions() throws RecognitionException, 
    					TokenStreamException {
      resetSkips();
      skipSorts();      
      skipPreds();      
      skipRuleSets();
      skipVars();
      skipTaclets(); 
      decls();
      resetSkips();
    }

    public void parsePredicates() throws RecognitionException, 
    					 TokenStreamException {
      resetSkips();
      skipSorts();
      skipFuncs();
      skipRuleSets();
      skipVars();
      skipTaclets();
      decls();
      resetSkips();
    }

    public void parseFuncAndPred() throws RecognitionException, 
    					  TokenStreamException {
      resetSkips();
      skipSorts(); 
      skipRuleSets();
      skipVars();
      skipTaclets();  
      decls();
      resetSkips();
    }    
    
    public void parseRuleSets() throws RecognitionException, 
    				       TokenStreamException {
      resetSkips();
      skipSorts();      
      skipFuncs(); 
      skipPreds(); 
      skipVars();
      skipTaclets();
      decls();
      resetSkips();
    }
    
    public void parseVariables() throws RecognitionException, 
                                        TokenStreamException {
      resetSkips();
      skipSorts();       
      skipFuncs(); 
      skipPreds(); 
      skipRuleSets();      
      skipTaclets();
      decls();
      resetSkips();
    }  

    public Term parseProblem() throws RecognitionException, 
    				      TokenStreamException {
      resetSkips();
      skipSorts(); 
      skipFuncs(); 
      skipPreds();
      skipRuleSets();
      //skipVars(); 
      skipTaclets();
      return problem();
    }

    public void parseIncludes() throws RecognitionException, 
    				        TokenStreamException {
      parse_includes=true;
      problem();
    }

    public void parseWith() throws RecognitionException, 
    				   TokenStreamException {
      onlyWith=true;
      problem();
    }

    private void schema_var_decl(String name, 
    				 Sort s, 
    				 boolean makeVariableSV,
            			 boolean makeSkolemTermSV,
            			 SchemaVariableModifierSet mods) 
            			 	throws AmbigiousDeclException {
        if (!skip_schemavariables) {
            SchemaVariable v;
            if(s == Sort.FORMULA && !makeSkolemTermSV) {
                v = SchemaVariableFactory.createFormulaSV(new Name(name), 
                					  mods.rigid());
            } else if(s == Sort.UPDATE) {
                v = SchemaVariableFactory.createUpdateSV(new Name(name));
            } else if(s instanceof ProgramSVSort) {
                v = SchemaVariableFactory.createProgramSV(
                		new ProgramElementName(name),
                		(ProgramSVSort) s,
                		mods.list());
            } else {
                if(makeVariableSV) {
                    v = SchemaVariableFactory.createVariableSV
                    (new Name(name), s);
                } else if(makeSkolemTermSV) {
                    v = SchemaVariableFactory.createSkolemTermSV(new Name(name), 
                    				                 s);
                } else { v = SchemaVariableFactory.createTermSV(
                					new Name(name), 
                					s, 
                					mods.rigid(), 
                					mods.strict());
                }
            }          

            if (inSchemaMode()) {
               if (variables().lookup(v.name()) != null) {
            	 throw new AmbigiousDeclException(v.name().toString(), 
            	 			          getFilename(), 
            	  				  getLine(), 
            	  				  getColumn());
               }
               variables().add(v);
            }
        }
    }

    public static Term toZNotation(String number, Namespace functions){    
	String s = number;
        final boolean negative = (s.charAt(0) == '-');
	if (negative) {
	    s = number.substring(1, s.length());
	}
        if(s.startsWith("0x")) {
	  try {
	    BigInteger bi = new BigInteger(s.substring(2),16);
	    s = bi.toString();
	  } catch(NumberFormatException nfe) {
	    Debug.fail("Not a hexadecimal constant (BTW, this should not have happened).");
	  }
	}
        Term result = tf.createTerm((Function)functions.lookup(new Name("#")));

        for(int i = 0; i<s.length(); i++){
            result = tf.createTerm((Function)functions.lookup(new Name(s.substring(i,i+1))), result);
        }

       	if (negative) {
  	    result = tf.createTerm((Function) functions.lookup(new Name("neglit")), result);
        }
	return tf.createTerm
            ((Function) functions.lookup(new Name("Z")), result); 
    }

    private String getTypeList(ImmutableList<ProgramVariable> vars) {
	StringBuffer result = new StringBuffer("");
	final Iterator<ProgramVariable> it = vars.iterator();
	while (it.hasNext()) {
         result.append(it.next().getContainerType().getFullName());
         if (it.hasNext()) result.append(", ");         
	}
	return result.toString();
    }

    private Operator getAttribute(Sort prefixSort, String attributeName) 
           throws SemanticException {
        final JavaInfo javaInfo = getJavaInfo();

        Operator result = null;
        
        if (inSchemaMode()) {
            // if we are currently reading taclets we look for schema variables first
            result = (SchemaVariable)variables().lookup(new Name(attributeName));
        }
        
        assert inSchemaMode() || result == null; 
        if (result == null) {
            
            final boolean unambigousAttributeName = attributeName.indexOf(':') != -1;

            if (unambigousAttributeName) {     
                result = javaInfo.getAttribute(attributeName);
            } else if(inSchemaMode() && attributeName.equals("length")) {
                try {
                    result = javaInfo.getArrayLength();
                } catch(Throwable e) {
                    semanticError("Getting array length failed");
                }
            } else if(attributeName.equals("<inv>")) {
                // The invariant observer "<inv>" is implicit and 
                // not part of the class declaration
                // A special case is needed, hence.
                result = javaInfo.getInvProgramVar();
            } else {
                if (inSchemaMode()) {
                    semanticError("Either undeclared schema variable '" + 
                                  attributeName + "' or a not fully qualified attribute in taclet.");
                }
                final KeYJavaType prefixKJT = javaInfo.getKeYJavaType(prefixSort);
                if (prefixKJT == null) {
                    semanticError("Could not find type '"+prefixSort+"'. Maybe mispelled or "+
                        "you use an array or object type in a .key-file with missing " + 
                        "\\javaSource section.");
                }
                // WATCHOUT why not in DECLARATION MODE	   
                if(!isDeclParser()) {			      	
                    final ImmutableList<ProgramVariable> vars = 	
                    javaInfo.getAllAttributes(attributeName, prefixKJT);

                    if (vars.size() == 0) {
                        semanticError("There is no attribute '" + attributeName + 
                            "' declared in type '" + prefixSort + "'");
                    }                    

                    if (LogicPrinter.printInShortForm(attributeName, 
                            prefixSort, getServices())) {       		   
                        result = vars.head();
                    } else {
                        if (vars.size() > 1) {
                            semanticError
                            ("Cannot uniquely determine attribute " + attributeName + 
                                "\n Please specify the exact type by attaching" +
                                " @( declaredInType ) to the attribute name." + 
                                "\n Found attributes of the same name in: " + getTypeList(vars));
                        }
                    }
                }              
            }
        }

        if ( result == null && !("length".equals(attributeName)) ) {
            throw new NotDeclException ("Attribute ", attributeName,
                getFilename(), getLine(), getColumn());
        }
        return result;
    }

   
    public Term createAttributeTerm(Term prefix, 
    				    Operator attribute) throws SemanticException {
        Term result = prefix;

        if (attribute instanceof SchemaVariable) {
            if (!inSchemaMode()) {
                semanticError("Schemavariables may only occur inside taclets.");
            }
	    SchemaVariable sv = (SchemaVariable) attribute;            
            if(sv.sort() instanceof ProgramSVSort 
                || sv.sort() == AbstractTermTransformer.METASORT) {
                semanticError("Cannot use schema variable " + sv + " as an attribute"); 
            }
            result = TermBuilder.DF.select(getServices(), 
                                           sv.sort(), 
                                           TermBuilder.DF.getBaseHeap(getServices()), 
                                           prefix, 
                                           tf.createTerm(attribute));
        } else {
            ProgramVariable pv = (ProgramVariable) attribute;
            if(pv instanceof ProgramConstant) {
                result = tf.createTerm(pv);
            } else if(pv == getServices().getJavaInfo().getArrayLength()) {
                result = TermBuilder.DF.dotLength(getServices(), result);
            } else {
            	Function fieldSymbol 
            		= getServices().getTypeConverter()
            		               .getHeapLDT()
            		               .getFieldSymbolForPV((LocationVariable)pv, 
            		                                    getServices());        
            	if (pv.isStatic()){
                    result = TermBuilder.DF.staticDot(getServices(), pv.sort(), fieldSymbol);
            	} else {            
                    result = TermBuilder.DF.dot(getServices(), pv.sort(), result, fieldSymbol);                
            	}
            }
        }
        return result;
    }

    private LogicVariable bindVar(String id, Sort s) {
        if(isGlobalDeclTermParser())
  	  Debug.fail("bindVar was called in Global Declaration Term parser.");
        LogicVariable v=new LogicVariable(new Name(id), s);
        namespaces().setVariables(variables().extended(v));
        return v;
    }

    private void bindVar(LogicVariable v) {
        if(isGlobalDeclTermParser())
  	  Debug.fail("bindVar was called in Global Declaration Term parser.");
        namespaces().setVariables(variables().extended(v));
    }

    private void bindVar() {
        if(isGlobalDeclTermParser())
  	  Debug.fail("bindVar was called in Global Declaration Term parser.");
        namespaces().setVariables ( new Namespace ( variables () ) );
    }

  private KeYJavaType getTypeByClassName(String s) 
    throws KeYSemanticException {
        KeYJavaType kjt = null;              
        try {
	    kjt=getJavaInfo().getKeYJavaTypeByClassName(s);
        } catch(RuntimeException e){
            return null;
        }

        return kjt;
    }
    
    private boolean isPackage(String name){
        try {   
            return getJavaInfo().isPackage(name);
        } catch(RuntimeException e){        
            // may be thrown in cases of invalid java identifiers
            return false;
        } 
    }
    
    private void unbindVars(Namespace orig) {
        if(isGlobalDeclTermParser()) {
            Debug.fail("unbindVars was called in Global Declaration Term parser.");
        }
        namespaces().setVariables(orig);
    }


    private Set progVars(JavaBlock jb) {
	if(isGlobalDeclTermParser()) {
  	  ProgramVariableCollector pvc
	      = new ProgramVariableCollector(jb.program(), getServices());
          pvc.start();
          return pvc.result();
        }else 
  	  if(!isDeclParser()) {
            if ((isTermParser() || isProblemParser()) && jb.isEmpty()) {
              return new HashSet();
            }   
            DeclarationProgramVariableCollector pvc
               = new DeclarationProgramVariableCollector(jb.program(), getServices());
            pvc.start();
            return pvc.result();
          }
	Debug.fail("KeYParser.progVars(): this statement should not be reachable.");
	return null;
    }

    private Term termForParsedVariable(ParsableVariable v) 
        throws antlr.SemanticException {
        if ( v instanceof LogicVariable || v instanceof ProgramVariable) {
            return tf.createTerm(v);
        } else {
	  if(isGlobalDeclTermParser())
		semanticError(v + " is not a logic variable");          
  	  if(isTermParser())
               semanticError(v + " is an unknown kind of variable.");
	  if (inSchemaMode() && v instanceof SchemaVariable ) {
               return tf.createTerm(v);
          } else {
	       String errorMessage = "";
               if ( inSchemaMode() ) {
       	         errorMessage += v +" is not a program, logic or schema variable";
               } else {
                 errorMessage += v +" is not a logic or program variable";
               }
               semanticError(errorMessage);
            }  
	}
	return null;
    }
    
    private PairOfStringAndJavaBlock getJavaBlock(Token t) throws antlr.SemanticException {
	PairOfStringAndJavaBlock sjb = new PairOfStringAndJavaBlock();
        String s=t.getText();
	int index = s.indexOf("\n");
	sjb.opName = s.substring(0,index);
	s = s.substring(index+1);
	Debug.out("Modal operator name passed to getJavaBlock: ",sjb.opName);
	Debug.out("Java block passed to getJavaBlock: ", s);

        JavaReader jr = javaReader;

	try {
            if (inSchemaMode()) {
                if(isProblemParser()) // Alt jr==null;
                jr = new SchemaRecoder2KeY(parserConfig.services(), 
                    parserConfig.namespaces());
                ((SchemaJavaReader)jr).setSVNamespace(variables());
            } else{
                if(isProblemParser()) // Alt jr==null;
                jr = new Recoder2KeY(parserConfig.services(), 
                    parserConfig.namespaces());
            }

            if (inSchemaMode() || isGlobalDeclTermParser()) {
                sjb.javaBlock = jr.readBlockWithEmptyContext(s);
            }else{
                sjb.javaBlock = jr.readBlockWithProgramVariables(programVariables(), s);
            }
        } catch (de.uka.ilkd.key.java.PosConvertException e) {
            lineOffset=e.getLine()-1;
            colOffset=e.getColumn()+1;
            throw new JavaParserException(e, t, 
                getFilename(), lineOffset, colOffset);
        } catch (de.uka.ilkd.key.java.ConvertException e) { 
            if (e.parseException()!=null
            &&  e.parseException().currentToken != null
            &&  e.parseException().currentToken.next != null) {               
                lineOffset=e.parseException().currentToken.next.beginLine;               
                colOffset=e.parseException().currentToken.next.beginColumn;
                e.parseException().currentToken.next.beginLine=getLine()-1;
                e.parseException().currentToken.next.beginColumn=getColumn();
                throw new JavaParserException(e, t, getFilename(), -1, -1);  // row/columns already in text
            }       
            if (e.proofJavaException()!=null
            &&  e.proofJavaException().currentToken != null
            &&  e.proofJavaException().currentToken.next != null) {      
                lineOffset = e.proofJavaException().currentToken.next.beginLine-1;
                colOffset=e.proofJavaException().currentToken.next.beginColumn;
                e.proofJavaException().currentToken.next.beginLine=getLine();
                e.proofJavaException().currentToken.next.beginColumn =getColumn();
                 throw  new JavaParserException(e, t, getFilename(), lineOffset, colOffset); 
                            
            }   
            throw new JavaParserException(e, t, getFilename());
        } 
        return sjb;
    }

    /**
     * looks up and returns the sort of the given name or null if none has been found.
     * If the sort is not found for the first time, the name is expanded with "java.lang." 
     * and the look up restarts
     */
     private Sort lookupSort(String name) throws SemanticException {
	Sort result = (Sort) sorts().lookup(new Name(name));
	if (result == null) {
	    if(name.equals(NullSort.NAME.toString())) {
	        Sort objectSort 
	        	= (Sort) sorts().lookup(new Name("java.lang.Object"));
	        if(objectSort == null) {
	            semanticError("Null sort cannot be used before "
	                          + "java.lang.Object is declared");
	        }
	        result = new NullSort(objectSort);
	        sorts().add(result);
	    } else {
  	    	result = (Sort) sorts().lookup(new Name("java.lang."+name));
  	    }
	}
	return result;
     }
     

    /** looks up a function, (program) variable or static query of the 
     * given name varfunc_id and the argument terms args in the namespaces 
     * and java info. 
     * @param varfunc_name the String with the symbols name
     * @param args is null iff no argument list is given, for instance `f', 
     * and is an array of size zero, if an empty argument list was given,
     * for instance `f()'.
     */
    private Operator lookupVarfuncId(String varfunc_name, Term[] args) 
        throws NotDeclException, SemanticException {

        // case 1: variable
        Operator v = (Operator) variables().lookup(new Name(varfunc_name));
        if (v != null && (args == null || (inSchemaMode() && v instanceof ModalOperatorSV))) {
            return v;
        }

        // case 2: program variable
        v = (Operator) programVariables().lookup
            (new ProgramElementName(varfunc_name));
        if (v != null && args==null) {
            return v;
        }
        
        // case 3: function
        v = (Operator) functions().lookup(new Name(varfunc_name));
        if (v != null) { // we allow both args==null (e.g. `c')
                         // and args.length=0 (e.g. 'c())' here 
            return v;
        }

        
        // case 4: instantiation of sort depending function
        int separatorIndex = varfunc_name.indexOf("::"); 
        if (separatorIndex > 0) {
            String sortName = varfunc_name.substring(0, separatorIndex);
            String baseName = varfunc_name.substring(separatorIndex + 2);
            Sort sort = lookupSort(sortName);
            SortDependingFunction firstInstance 
            	= SortDependingFunction.getFirstInstance(new Name(baseName), 
            					         getServices());
                        
            if(sort != null && firstInstance != null) {
                v = firstInstance.getInstanceFor(sort, getServices());
                if(v != null) {
                    return v;
                }
            } 
        }
        
        // not found
        if (args==null) {
            throw new NotDeclException
                ("(program) variable or constant", varfunc_name,
                 getFilename(), getLine(), getColumn());
        } else {
            throw new NotDeclException
                ("function or static query", varfunc_name,
                 getFilename(), getLine(), getColumn());
        }
    }

    private boolean isStaticAttribute() throws KeYSemanticException {	
        if(inSchemaMode()) return false;
        final JavaInfo javaInfo = getJavaInfo();
        KeYJavaType kjt = null;
	boolean result = false;
        try {
            int n = 1; 
            StringBuffer className = new StringBuffer(LT(n).getText());
	    while (isPackage(className.toString()) || LA(n+2)==NUM_LITERAL || 
	    		(LT(n+2)!=null && LT(n+2).getText()!=null && 
	    		LT(n+2).getText().charAt(0)<='Z' && LT(n+2).getText().charAt(0)>='A' && 
	    		(LT(n+2).getText().length()==1 || 
	    		 LT(n+2).getText().charAt(1)<='z' && LT(n+2).getText().charAt(1)>='a'))){  	   
                if (LA(n+1) != DOT && LA(n+1) != EMPTYBRACKETS) return false;
                // maybe still an attribute starting with an uppercase letter followed by a lowercase letter
                if(getTypeByClassName(className.toString())!=null){
                    ProgramVariable maybeAttr = 
                    javaInfo.getAttribute(LT(n+2).getText(), getTypeByClassName(className.toString()));
                    if(maybeAttr!=null){
                        return true;
                    }
                }
                className.append(".");	       
                className.append(LT(n+2).getText());
                n+=2;
	    }	
        while (LA(n+1) == EMPTYBRACKETS) {
                className.append("[]");
                n++;
        }
	kjt = getTypeByClassName(className.toString());

	    if (kjt != null) { 
		// works as we do not have inner classes
		if (LA(n+1) == DOT) {
		    final ProgramVariable pv = 
		      javaInfo.getAttribute(LT(n+2).getText(), kjt);
		    result = (pv != null && pv.isStatic());		
		}    
	    }else{
	     result = false;
	    }
	} catch (antlr.TokenStreamException tse) {
	    // System.out.println("an exception occured"+tse);
	    result = false;
	}
	if(result && inputState.guessing > 0) {
           savedGuessing = inputState.guessing;
	   inputState.guessing = 0;
	}
	return result;
    }

    private boolean isTermTransformer() throws TokenStreamException {  
    if((LA(1) == IDENT &&
         AbstractTermTransformer.name2metaop(LT(1).getText())!=null)
       || LA(1) == IN_TYPE)
      return true;
    return false;
    }

    private boolean isStaticQuery() throws KeYSemanticException {   
    if(inSchemaMode()) return false;
    final JavaInfo javaInfo = getJavaInfo();
    boolean result = false;
    try {
        int n = 1; 
        KeYJavaType kjt = null;
        StringBuffer className = new StringBuffer(LT(n).getText());
        while (isPackage(className.toString())) {          
          if (LA(n+1) != DOT) return false;
          className.append(".");         
          className.append(LT(n+2).getText());
          n+=2;
        }   
        kjt = getTypeByClassName(className.toString());
        if (kjt != null) { 
           if (LA(n+1) == DOT && LA(n+3) == LPAREN) {
               Iterator<IProgramMethod> it = javaInfo.getAllProgramMethods(kjt).iterator();
               while(it.hasNext()) {
                 final IProgramMethod pm = it.next();
                 final String name = kjt.getFullName()+"::"+LT(n+2).getText();                 
                 if(pm != null && pm.isStatic() && pm.name().toString().equals(name) ) {
                   result = true;
		   break;
		 }
               }
           }   
        }
    } catch (antlr.TokenStreamException tse) {
        result = false;
    }
    if(result && inputState.guessing > 0) {
      savedGuessing = inputState.guessing;
      inputState.guessing = 0;
    }
    return result;
    }


    private TacletBuilder createTacletBuilderFor
        (Object find, int applicationRestriction) 
        throws InvalidFindException {
        if ( applicationRestriction != RewriteTaclet.NONE && !( find instanceof Term ) ) {        
            String mod = "";
            if ((applicationRestriction & RewriteTaclet.SAME_UPDATE_LEVEL) != 0) {
                mod = "\"\\sameUpdateLevel\"";
            }
            if ((applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) != 0) {
                if (mod != "") mod += " and ";
                mod += "\"\\inSequentState\""; 
            }
            if ((applicationRestriction & RewriteTaclet.ANTECEDENT_POLARITY) != 0) {
                if (mod != "") mod += " and ";
                mod += "\"\\antecedentPolarity\""; 
            }
            if ((applicationRestriction & RewriteTaclet.SUCCEDENT_POLARITY) != 0) {
                if (mod != "") mod += " and ";
                mod += "\"\\succedentPolarity\"";
            }
            if (mod == "") {
                mod = "Application restrictions";               
            }
            
            throw new InvalidFindException
                ( mod +  " may only be used for rewrite taclets:" + find,
                 getFilename(), getLine(), getColumn());
        }
        if ( find == null ) {
            return new NoFindTacletBuilder();
        } else if ( find instanceof Term ) {
            return new RewriteTacletBuilder().setFind((Term)find)
                .setApplicationRestriction(applicationRestriction);
        } else if ( find instanceof Sequent ) {
            Sequent findSeq = (Sequent) find;
            if ( findSeq.isEmpty() ) {
                return new NoFindTacletBuilder();
            } else if (   findSeq.antecedent().size() == 1
                          && findSeq.succedent().size() == 0 ) {
                Term findFma = findSeq.antecedent().get(0).formula();
                return new AntecTacletBuilder().setFind(findFma);
            } else if (   findSeq.antecedent().size() == 0
                          && findSeq.succedent().size() == 1 ) {
                Term findFma = findSeq.succedent().get(0).formula();
                return new SuccTacletBuilder().setFind(findFma);
            } else {
                throw new InvalidFindException
                    ("Unknown find-sequent (perhaps null?):"+findSeq,
                     getFilename(), getLine(), getColumn());
            }
        } else {
            throw new InvalidFindException
                    ("Unknown find class type: " + find.getClass().getName(),
                     getFilename(), getLine(), getColumn());
        }
    }       

    private void addGoalTemplate(TacletBuilder b,
                                 String id,
                                 Object rwObj,
                                 Sequent addSeq,
                                 ImmutableList<Taclet> addRList,
                                 ImmutableSet<SchemaVariable> pvs,
                                 ImmutableSet<Choice> soc) 
        throws SemanticException
        {
            TacletGoalTemplate gt = null;
            if ( rwObj == null ) {
                // there is no replacewith, so we take
                gt = new TacletGoalTemplate(addSeq,
                                            addRList,
                                            pvs);
            } else {
                if ( b instanceof NoFindTacletBuilder ) {
                    // there is a replacewith without a find.
                    throw 
                        new UnfittingReplacewithException
                        ("Replacewith without find", getFilename(),
                         getLine(), getColumn());
                } else if ( b instanceof SuccTacletBuilder
                            || b instanceof AntecTacletBuilder ) {
                    if ( rwObj instanceof Sequent ) {
                        gt = new AntecSuccTacletGoalTemplate(addSeq,
                                                             addRList,
                                                             (Sequent)rwObj,
                                                             pvs);  
                    } else {
                        throw new UnfittingReplacewithException
                            ("Replacewith in a Antec-or SuccTaclet has "+
                             "to contain a sequent (not a term)", 
                             getFilename(), getLine(), getColumn());
                    }
                } else if ( b instanceof RewriteTacletBuilder ) {
                    if ( rwObj instanceof Term ) {
                        gt = new RewriteTacletGoalTemplate(addSeq,
                                                           addRList,
                                                           (Term)rwObj,
                                                           pvs);  
                    } else {
                        throw new UnfittingReplacewithException
                            ("Replacewith in a RewriteTaclet has "+
                             "to contain a term (not a sequent)", 
                             getFilename(), getLine(), getColumn());
                    }
                }
            }
            gt.setName(id); 
            b.addTacletGoalTemplate(gt);
            if(soc != null) b.addGoal2ChoicesMapping(gt,soc);
        }
     
    public void testLiteral(String l1, String l2)
    throws KeYSemanticException
    {
     if (!l1.equals(l2)){
        semanticError("Expecting '"+l1+"', found '"+l2+"'.");
	};
    }

    /** parses a problem but without reading the declarations of
     * sorts, functions and predicates. These have to be given
     * explicitly.
     * the rule sets of the current problem file will be added 
     */ 
    public Term parseTacletsAndProblem() 
    throws antlr.RecognitionException, antlr.TokenStreamException{
        resetSkips();
        skipSorts(); skipFuncs(); skipPreds();    
        return problem();
    }

    /**
     * returns the ProgramMethod parsed in the jml_specifications section.
     */
    public IProgramMethod getProgramMethod(){
        return pm;
    }


    public void addFunction(Function f) {
        functions().add(f);
    }

    
    private ImmutableSet<Modality> lookupOperatorSV(String opName, ImmutableSet<Modality> modalities) 
    		throws KeYSemanticException {
	ModalOperatorSV osv = (ModalOperatorSV)variables().lookup(new Name(opName));
        if(osv == null) {
	    semanticError("Schema variable "+opName+" not defined.");
	}
        modalities = modalities.union(osv.getModalities());
        return modalities;
    } 
    
    private ImmutableSet<Modality> opSVHelper(String opName, 
                                     ImmutableSet<Modality> modalities) 
        	throws KeYSemanticException {
        if(opName.charAt(0) == '#') {
            return lookupOperatorSV(opName, modalities);           
        } else {
	    switchToNormalMode();
       	    Modality m = Modality.getModality(opName);
	    switchToSchemaMode();
            if(m == null) {
                semanticError("Unrecognised operator: "+opName);
            }
            modalities = modalities.add(m);
       }
       return modalities;
    }

    private void semanticError(String message) throws KeYSemanticException {
      throw new KeYSemanticException
        (message, getFilename(), getLine(), getColumn());
    }

    private static class PairOfStringAndJavaBlock {
      String opName;
      JavaBlock javaBlock;
    }


protected KeYParser(TokenBuffer tokenBuf, int k) {
  super(tokenBuf,k);
  tokenNames = _tokenNames;
}

public KeYParser(TokenBuffer tokenBuf) {
  this(tokenBuf,1);
}

protected KeYParser(TokenStream lexer, int k) {
  super(lexer,k);
  tokenNames = _tokenNames;
}

public KeYParser(TokenStream lexer) {
  this(lexer,1);
}

public KeYParser(ParserSharedInputState state) {
  super(state,1);
  tokenNames = _tokenNames;
}

	public final void top() throws RecognitionException, TokenStreamException {
		
		Term a;
		
		try {      // for error handling
			a=formula();
			if ( inputState.guessing==0 ) {
					 
				Debug.fail("KeYParser: top() should not be called. Ever.");	 
				
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
	}
	
/**
 * In the special but important case of Taclets, we don't yet know
 * whether we are going to have a term or a formula, and it is hard
 * to decide a priori what we are looking at.  So the `term' 
 * non-terminal will recognize a term or a formula.  The `formula'
 * reads a formula/term and throws an error if it wasn't a formula.
 * This gives a rather late error message. */
	public final Term  formula() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		try {      // for error handling
			a=term();
			if ( inputState.guessing==0 ) {
				
				if (a != null && a.sort() != Sort.FORMULA ) {
				semanticError("Just Parsed a Term where a Formula was expected.");
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_1);
			} else {
			  throw ex;
			}
		}
		return a;
	}
	
	public final void decls() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			_loop4:
			do {
				if ((LA(1)==INCLUDE||LA(1)==INCLUDELDTS)) {
					one_include_statement();
				}
				else {
					break _loop4;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
				if(parse_includes) return;
				activatedChoices = DefaultImmutableSet.<Choice>nil();  
					
			}
			{
			switch ( LA(1)) {
			case WITHOPTIONS:
			{
				options_choice();
				break;
			}
			case EOF:
			case SORTS:
			case SCHEMAVARIABLES:
			case PROGRAMVARIABLES:
			case OPTIONSDECL:
			case HEURISTICSDECL:
			case PREDICATES:
			case FUNCTIONS:
			case RULES:
			case PROBLEM:
			case CHOOSECONTRACT:
			case PROOFOBLIGATION:
			case CONTRACTS:
			case INVARIANTS:
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
			_loop7:
			do {
				switch ( LA(1)) {
				case PREDICATES:
				{
					pred_decls();
					break;
				}
				case FUNCTIONS:
				{
					func_decls();
					break;
				}
				default:
					if (((LA(1)==OPTIONSDECL))&&(!onlyWith)) {
						option_decls();
					}
					else if (((LA(1)==SORTS))&&(!onlyWith)) {
						sort_decls();
					}
					else if (((LA(1)==PROGRAMVARIABLES))&&(!onlyWith)) {
						prog_var_decls();
					}
					else if (((LA(1)==SCHEMAVARIABLES))&&(!onlyWith)) {
						schema_var_decls();
					}
					else if (((LA(1)==HEURISTICSDECL))&&(!onlyWith)) {
						ruleset_decls();
					}
				else {
					break _loop7;
				}
				}
			} while (true);
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
	}
	
	public final void one_include_statement() throws RecognitionException, TokenStreamException {
		
		
		boolean ldts = false;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case INCLUDE:
			{
				match(INCLUDE);
				break;
			}
			case INCLUDELDTS:
			{
				{
				match(INCLUDELDTS);
				if ( inputState.guessing==0 ) {
					ldts = true;
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
			one_include(ldts);
			{
			_loop12:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					one_include(ldts);
				}
				else {
					break _loop12;
				}
				
			} while (true);
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void options_choice() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			match(WITHOPTIONS);
			activated_choice();
			{
			_loop18:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					activated_choice();
				}
				else {
					break _loop18;
				}
				
			} while (true);
			}
			match(SEMI);
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
	}
	
	public final void option_decls() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(OPTIONSDECL);
			match(LBRACE);
			{
			_loop22:
			do {
				if ((LA(1)==IDENT)) {
					choice();
					match(SEMI);
				}
				else {
					break _loop22;
				}
				
			} while (true);
			}
			match(RBRACE);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void sort_decls() throws RecognitionException, TokenStreamException {
		
		
		ImmutableList<Sort> lsorts = ImmutableSLList.<Sort>nil();
		ImmutableList<Sort> multipleSorts = ImmutableSLList.<Sort>nil();
		
		
		try {      // for error handling
			match(SORTS);
			match(LBRACE);
			{
			_loop30:
			do {
				if ((LA(1)==GENERIC||LA(1)==ABSTRACT||LA(1)==IDENT)) {
					multipleSorts=one_sort_decl();
					if ( inputState.guessing==0 ) {
						lsorts = lsorts.prepend(multipleSorts);
					}
				}
				else {
					break _loop30;
				}
				
			} while (true);
			}
			match(RBRACE);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void prog_var_decls() throws RecognitionException, TokenStreamException {
		
		
		String var_name;
		KeYJavaType kjt = null;
		ImmutableList<String> var_names = null;
		
		
		try {      // for error handling
			if ( inputState.guessing==0 ) {
				switchToNormalMode();
			}
			match(PROGRAMVARIABLES);
			match(LBRACE);
			{
			_loop55:
			do {
				if ((LA(1)==IDENT)) {
					kjt=keyjavatype();
					var_names=simple_ident_comma_list();
					if ( inputState.guessing==0 ) {
						
							        Iterator<String> it = var_names.iterator();
								while(it.hasNext()){
								  var_name = it.next();
								  ProgramElementName pvName = new ProgramElementName(var_name);
								  Named name = lookup(pvName);
						if (name != null ) {
								    // commented out as pv do not have unique name (at the moment)
								    //  throw new AmbigiousDeclException
								    //  	(var_name, getFilename(), getLine(), getColumn());
								    if(!(name instanceof ProgramVariable) || (name instanceof ProgramVariable && 
									    !((ProgramVariable)name).getKeYJavaType().equals(kjt))) { 
						namespaces().programVariables().add(new LocationVariable
						(pvName, kjt));
								    }
						}else{
						namespaces().programVariables().add(new LocationVariable
						(pvName, kjt));
								  }
							       }
						
					}
					match(SEMI);
				}
				else {
					break _loop55;
				}
				
			} while (true);
			}
			match(RBRACE);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_5);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void schema_var_decls() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(SCHEMAVARIABLES);
			match(LBRACE);
			if ( inputState.guessing==0 ) {
				switchToSchemaMode();
			}
			{
			_loop63:
			do {
				if (((LA(1) >= MODALOPERATOR && LA(1) <= SKOLEMFORMULA))) {
					one_schema_var_decl();
				}
				else {
					break _loop63;
				}
				
			} while (true);
			}
			match(RBRACE);
			if ( inputState.guessing==0 ) {
				switchToNormalMode();
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
	}
	
	public final void pred_decls() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(PREDICATES);
			match(LBRACE);
			{
			_loop86:
			do {
				if ((LA(1)==IDENT)) {
					pred_decl();
				}
				else {
					break _loop86;
				}
				
			} while (true);
			}
			match(RBRACE);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void func_decls() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(FUNCTIONS);
			match(LBRACE);
			{
			_loop93:
			do {
				if ((LA(1)==UNIQUE||LA(1)==IDENT)) {
					func_decl();
				}
				else {
					break _loop93;
				}
				
			} while (true);
			}
			match(RBRACE);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void ruleset_decls() throws RecognitionException, TokenStreamException {
		
		
		String id = null;
		
		
		try {      // for error handling
			match(HEURISTICSDECL);
			match(LBRACE);
			{
			_loop106:
			do {
				if ((LA(1)==IDENT)) {
					id=simple_ident();
					match(SEMI);
					if ( inputState.guessing==0 ) {
						
						if (!skip_rulesets) {
						RuleSet h = new RuleSet(new Name(id));
						if(ruleSets().lookup(new Name(id))==null){
						ruleSets().add(h);
						}
						}
						
					}
				}
				else {
					break _loop106;
				}
				
			} while (true);
			}
			match(RBRACE);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_4);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void one_include(
		boolean ldt
	) throws RecognitionException, TokenStreamException {
		
		Token  absfile = null;
		
		String relfile = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case IDENT:
			{
				absfile = LT(1);
				match(IDENT);
				if ( inputState.guessing==0 ) {
					
					if(parse_includes){
					addInclude(absfile.getText(),false,ldt);
					}
					
				}
				break;
			}
			case STRING_LITERAL:
			{
				relfile=string_literal();
				if ( inputState.guessing==0 ) {
					
					if(parse_includes){
					addInclude(relfile, true,ldt);
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
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_6);
			} else {
			  throw ex;
			}
		}
	}
	
	public final String  string_literal() throws RecognitionException, TokenStreamException {
		String lit = null;
		
		Token  id = null;
		
		try {      // for error handling
			id = LT(1);
			match(STRING_LITERAL);
			if ( inputState.guessing==0 ) {
				
				lit = id.getText();
				lit = lit.substring(1,lit.length()-1);
				stringLiteralLine = id.getLine();
				
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
		return lit;
	}
	
	public final void activated_choice() throws RecognitionException, TokenStreamException {
		
		Token  cat = null;
		Token  choice = null;
		
		String name;
		Choice c;
		
		
		try {      // for error handling
			cat = LT(1);
			match(IDENT);
			match(COLON);
			choice = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				if(usedChoiceCategories.contains(cat.getText())){
				throw new IllegalArgumentException("You have already chosen a different option for "+cat.getText());
				}
				usedChoiceCategories.add(cat.getText());
				name = cat.getText()+":"+choice.getText();
				c = (Choice) choices().lookup(new Name(name));
				if(c==null){
				throw new NotDeclException("Option", choice,
				getFilename());
				}else{
				activatedChoices=activatedChoices.add(c);
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_6);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void choice() throws RecognitionException, TokenStreamException {
		
		Token  category = null;
		
		String cat=null;
		
		
		try {      // for error handling
			category = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				cat=category.getText();
			}
			{
			switch ( LA(1)) {
			case COLON:
			{
				match(COLON);
				match(LBRACE);
				choice_option(cat);
				{
				_loop26:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						choice_option(cat);
					}
					else {
						break _loop26;
					}
					
				} while (true);
				}
				match(RBRACE);
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
			if ( inputState.guessing==0 ) {
				
				if(!category2Default.containsKey(cat)){
				choices().add(new Choice("On",cat));
				choices().add(new Choice("Off",cat)); 
				category2Default.put(cat, cat+":On");               
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
	}
	
	public final void choice_option(
		String cat
	) throws RecognitionException, TokenStreamException {
		
		Token  choice = null;
		
		String name;
		
		
		try {      // for error handling
			choice = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				name=cat+":"+choice.getText();
				Choice c = (Choice) choices().lookup(new Name(name));
				if(c==null){
				c = new Choice(choice.getText(),cat);
				choices().add(c);
				}
				if(!category2Default.containsKey(cat)){
				category2Default.put(cat, name);
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_9);
			} else {
			  throw ex;
			}
		}
	}
	
	public final ImmutableList<Sort>  one_sort_decl() throws RecognitionException, TokenStreamException {
		ImmutableList<Sort> createdSorts = ImmutableSLList.<Sort>nil();
		
		
		boolean isAbstractSort = false;
		boolean isGenericSort = false;
		Sort[] sortExt=new Sort [0];
		Sort[] sortOneOf=new Sort [0];
		String firstSort;
		ImmutableList<String> sortIds = ImmutableSLList.<String>nil(); 
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case GENERIC:
			{
				match(GENERIC);
				if ( inputState.guessing==0 ) {
					isGenericSort=true;
				}
				sortIds=simple_ident_comma_list();
				{
				switch ( LA(1)) {
				case ONEOF:
				{
					match(ONEOF);
					sortOneOf=oneof_sorts();
					break;
				}
				case EXTENDS:
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
				{
				switch ( LA(1)) {
				case EXTENDS:
				{
					match(EXTENDS);
					sortExt=extends_sorts();
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
				break;
			}
			case ABSTRACT:
			case IDENT:
			{
				{
				switch ( LA(1)) {
				case ABSTRACT:
				{
					match(ABSTRACT);
					if ( inputState.guessing==0 ) {
						isAbstractSort = true;
					}
					break;
				}
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
				firstSort=simple_ident_dots();
				if ( inputState.guessing==0 ) {
					sortIds = sortIds.prepend(firstSort);
				}
				{
				switch ( LA(1)) {
				case EXTENDS:
				{
					{
					match(EXTENDS);
					sortExt=extends_sorts();
					}
					break;
				}
				case COMMA:
				{
					{
					{
					match(COMMA);
					}
					sortIds=simple_ident_comma_list();
					if ( inputState.guessing==0 ) {
						sortIds = sortIds.prepend(firstSort) ;
					}
					}
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
				
				if (!skip_sorts) {
				Iterator<String> it = sortIds.iterator ();        
				while ( it.hasNext () ) {
				Name sort_name = new Name(it.next());   
				// attention: no expand to java.lang here!       
				if (sorts().lookup(sort_name) == null) {
				Sort s;
							    if (isGenericSort) {
				int i;
				ImmutableSet<Sort>  ext   = DefaultImmutableSet.<Sort>nil();
				ImmutableSet<Sort>  oneOf = DefaultImmutableSet.<Sort>nil();
				
				for ( i = 0; i != sortExt.length; ++i )
				ext = ext.add ( sortExt[i] );
				
				for ( i = 0; i != sortOneOf.length; ++i )
				oneOf = oneOf.add ( sortOneOf[i] );
				
				try {
				s = new GenericSort(sort_name, ext, oneOf);
				} catch (GenericSupersortException e) {
				throw new GenericSortException ( "sort", "Illegal sort given",
				e.getIllegalSort(), getFilename(), getLine(), getColumn());
				}
				} else if (new Name("any").equals(sort_name)) {
				s = Sort.ANY;
				} else  {
				ImmutableSet<Sort>  ext = DefaultImmutableSet.<Sort>nil();
				
				for ( int i = 0; i != sortExt.length; ++i ) {
				ext = ext.add ( sortExt[i] );
				}
				
				s = new SortImpl(sort_name, ext, isAbstractSort);
				}
				assert s != null;
				sorts().add ( s ); 
				
				createdSorts = createdSorts.append(s);
				}
				}
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_10);
			} else {
			  throw ex;
			}
		}
		return createdSorts;
	}
	
	public final ImmutableList<String>  simple_ident_comma_list() throws RecognitionException, TokenStreamException {
		ImmutableList<String> ids = ImmutableSLList.<String>nil();
		
		
		String id = null;
		
		
		try {      // for error handling
			id=simple_ident();
			if ( inputState.guessing==0 ) {
				ids = ids.append(id);
			}
			{
			_loop60:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					id=simple_ident();
					if ( inputState.guessing==0 ) {
						ids = ids.append(id);
					}
				}
				else {
					break _loop60;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_11);
			} else {
			  throw ex;
			}
		}
		return ids;
	}
	
	public final Sort[]  oneof_sorts() throws RecognitionException, TokenStreamException {
		Sort[] oneOfSorts = null;
		
		
		List args = new LinkedList();
		Sort s;
		
		
		try {      // for error handling
			match(LBRACE);
			s=sortId_check(true);
			if ( inputState.guessing==0 ) {
				args.add(s);
			}
			{
			_loop49:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					s=sortId_check(true);
					if ( inputState.guessing==0 ) {
						args.add(s);
					}
				}
				else {
					break _loop49;
				}
				
			} while (true);
			}
			match(RBRACE);
			if ( inputState.guessing==0 ) {
				
				oneOfSorts = (Sort[])args.toArray(AN_ARRAY_OF_SORTS);
				
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
		return oneOfSorts;
	}
	
	public final Sort[]  extends_sorts() throws RecognitionException, TokenStreamException {
		Sort[] extendsSorts = null;
		
		
		List args = new LinkedList();
		Sort s;
		
		
		try {      // for error handling
			s=any_sortId_check(!skip_sorts);
			if ( inputState.guessing==0 ) {
				args.add(s);
			}
			{
			_loop46:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					s=any_sortId_check(!skip_sorts);
					if ( inputState.guessing==0 ) {
						args.add(s);
					}
				}
				else {
					break _loop46;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
				extendsSorts = (Sort[])args.toArray(AN_ARRAY_OF_SORTS);
				
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
		return extendsSorts;
	}
	
	public final String  simple_ident_dots() throws RecognitionException, TokenStreamException {
		 String ident = ""; ;
		
		Token  num = null;
		
		String id = null;
		
		
		try {      // for error handling
			id=simple_ident();
			if ( inputState.guessing==0 ) {
				ident += id;
			}
			{
			_loop43:
			do {
				if ((LA(1)==DOT)) {
					match(DOT);
					{
					switch ( LA(1)) {
					case IDENT:
					{
						id=simple_ident();
						break;
					}
					case NUM_LITERAL:
					{
						num = LT(1);
						match(NUM_LITERAL);
						if ( inputState.guessing==0 ) {
							id=num.getText();
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
						ident += "." + id;
					}
				}
				else {
					break _loop43;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_13);
			} else {
			  throw ex;
			}
		}
		return ident;
	}
	
	public final String  simple_ident() throws RecognitionException, TokenStreamException {
		String ident = null;
		
		Token  id = null;
		
		try {      // for error handling
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				ident = id.getText();
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_14);
			} else {
			  throw ex;
			}
		}
		return ident;
	}
	
	public final Sort  any_sortId_check(
		boolean checkSort
	) throws RecognitionException, TokenStreamException {
		Sort s = null;
		
		
		Pair<Sort,Type> p;
		
		
		try {      // for error handling
			p=any_sortId_check_help(checkSort);
			s=array_decls(p, checkSort);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_15);
			} else {
			  throw ex;
			}
		}
		return s;
	}
	
	public final Sort  sortId_check(
		boolean checkSort
	) throws RecognitionException, TokenStreamException {
		Sort s = null;
		
		
		Pair<Sort,Type> p;
		
		
		try {      // for error handling
			p=sortId_check_help(checkSort);
			s=array_decls(p, checkSort);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_16);
			} else {
			  throw ex;
			}
		}
		return s;
	}
	
	public final KeYJavaType  keyjavatype() throws RecognitionException, TokenStreamException {
		KeYJavaType kjt=null;
		
		
		String type = null;
		boolean array = false;
		
		
		try {      // for error handling
			type=simple_ident_dots();
			{
			_loop52:
			do {
				if ((LA(1)==EMPTYBRACKETS)) {
					match(EMPTYBRACKETS);
					if ( inputState.guessing==0 ) {
						type += "[]"; array=true;
					}
				}
				else {
					break _loop52;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
				kjt = getJavaInfo().getKeYJavaType(type);
				
				//expand to "java.lang"            
				if (kjt == null) {
				try {
				String guess = "java.lang." + type;
					        kjt = getJavaInfo().getKeYJavaType(guess);
					    } catch(Exception e) {
					        kjt = null;
					    }
				}
				
				//arrays
				if(kjt == null && array) {
				try {
				JavaBlock jb = getJavaInfo().readJavaBlock("{" + type + " k;}");
				kjt = ((VariableDeclaration) 
				((StatementBlock) jb.program()).getChildAt(0)).
				getTypeReference().getKeYJavaType();
				} catch (Exception e) {
				kjt = null;
				}          
				}
				
				//try as sort without Java type (neede e.g. for "Heap")
				if(kjt == null) {
					    Sort sort = lookupSort(type);
					    if(sort != null) {
				kjt = new KeYJavaType(null, sort);
				}
				}
				
				if(kjt == null) {
				semanticError("Unknown type: " + type);
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_17);
			} else {
			  throw ex;
			}
		}
		return kjt;
	}
	
	public final void one_schema_var_decl() throws RecognitionException, TokenStreamException {
		
		
		Sort s = null;
		boolean makeVariableSV  = false;
		boolean makeSkolemTermSV = false;
		String id = null;
		String parameter = null;
		String nameString = null;
		ImmutableList<String> ids = null;
		SchemaVariableModifierSet mods = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case MODALOPERATOR:
			{
				{
				match(MODALOPERATOR);
				one_schema_modal_op_decl();
				match(SEMI);
				}
				break;
			}
			case PROGRAM:
			case FORMULA:
			case TERM:
			case UPDATE:
			case VARIABLES:
			case SKOLEMTERM:
			case SKOLEMFORMULA:
			{
				{
				{
				switch ( LA(1)) {
				case PROGRAM:
				{
					match(PROGRAM);
					if ( inputState.guessing==0 ) {
						mods = new SchemaVariableModifierSet.ProgramSV ();
					}
					{
					switch ( LA(1)) {
					case LBRACKET:
					{
						schema_modifiers(mods);
						break;
					}
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
					id=simple_ident();
					{
					switch ( LA(1)) {
					case LBRACKET:
					{
						match(LBRACKET);
						nameString=simple_ident();
						match(EQUALS);
						parameter=simple_ident_dots();
						match(RBRACKET);
						break;
					}
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
					if ( inputState.guessing==0 ) {
						
						if(nameString != null && !"name".equals(nameString)) {
						semanticError("Unrecognized token '"+nameString+"', expected 'name'");
						}
						ProgramSVSort psv = ProgramSVSort.name2sort().get(new Name(id));
						s = (Sort) (parameter != null ? psv.createInstance(parameter) : psv);
						if (s == null) {
						semanticError
						("Program SchemaVariable of type "+id+" not found.");
						}
						
					}
					ids=simple_ident_comma_list();
					break;
				}
				case FORMULA:
				{
					match(FORMULA);
					if ( inputState.guessing==0 ) {
						mods = new SchemaVariableModifierSet.FormulaSV ();
					}
					{
					switch ( LA(1)) {
					case LBRACKET:
					{
						schema_modifiers(mods);
						break;
					}
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
					if ( inputState.guessing==0 ) {
						s = Sort.FORMULA;
					}
					ids=simple_ident_comma_list();
					break;
				}
				case UPDATE:
				{
					match(UPDATE);
					if ( inputState.guessing==0 ) {
						mods = new SchemaVariableModifierSet.FormulaSV ();
					}
					{
					switch ( LA(1)) {
					case LBRACKET:
					{
						schema_modifiers(mods);
						break;
					}
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
					if ( inputState.guessing==0 ) {
						s = Sort.UPDATE;
					}
					ids=simple_ident_comma_list();
					break;
				}
				case SKOLEMFORMULA:
				{
					match(SKOLEMFORMULA);
					if ( inputState.guessing==0 ) {
						makeSkolemTermSV = true;
					}
					if ( inputState.guessing==0 ) {
						mods = new SchemaVariableModifierSet.FormulaSV ();
					}
					{
					switch ( LA(1)) {
					case LBRACKET:
					{
						schema_modifiers(mods);
						break;
					}
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
					if ( inputState.guessing==0 ) {
						s = Sort.FORMULA;
					}
					ids=simple_ident_comma_list();
					break;
				}
				case TERM:
				case VARIABLES:
				case SKOLEMTERM:
				{
					{
					switch ( LA(1)) {
					case TERM:
					{
						match(TERM);
						if ( inputState.guessing==0 ) {
							mods = new SchemaVariableModifierSet.TermSV ();
						}
						{
						switch ( LA(1)) {
						case LBRACKET:
						{
							schema_modifiers(mods);
							break;
						}
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
						break;
					}
					case VARIABLES:
					{
						{
						match(VARIABLES);
						if ( inputState.guessing==0 ) {
							makeVariableSV = true;
						}
						if ( inputState.guessing==0 ) {
							mods = new SchemaVariableModifierSet.VariableSV ();
						}
						{
						switch ( LA(1)) {
						case LBRACKET:
						{
							schema_modifiers(mods);
							break;
						}
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
						}
						break;
					}
					case SKOLEMTERM:
					{
						{
						match(SKOLEMTERM);
						if ( inputState.guessing==0 ) {
							makeSkolemTermSV = true;
						}
						if ( inputState.guessing==0 ) {
							mods = new SchemaVariableModifierSet.SkolemTermSV ();
						}
						{
						switch ( LA(1)) {
						case LBRACKET:
						{
							schema_modifiers(mods);
							break;
						}
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
						}
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					s=any_sortId_check(true);
					ids=simple_ident_comma_list();
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
					
					Iterator<String> it = ids.iterator();
					while(it.hasNext())
					schema_var_decl(it.next(),
					s,
					makeVariableSV,
					makeSkolemTermSV, 
							       mods);
					
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
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_18);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void one_schema_modal_op_decl() throws RecognitionException, TokenStreamException {
		
		
		ImmutableSet<Modality> modalities = DefaultImmutableSet.<Modality>nil();
		String id = null;
		Sort sort = Sort.FORMULA;
		ImmutableList<String> ids = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				sort=any_sortId_check(true);
				if ( inputState.guessing==0 ) {
					
					if (sort != Sort.FORMULA) { 
					semanticError("Modal operator SV must be a FORMULA, not " + sort);
					}            
					
				}
				match(RPAREN);
				break;
			}
			case LBRACE:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(LBRACE);
			ids=simple_ident_comma_list();
			match(RBRACE);
			id=simple_ident();
			if ( inputState.guessing==0 ) {
				if (skip_schemavariables) {	       
					       return;
					    }	        
				Iterator<String> it1 = ids.iterator();
				while(it1.hasNext()) {
					      modalities = opSVHelper(it1.next(), modalities);
					    }
				SchemaVariable osv = (SchemaVariable)variables().lookup(new Name(id));
				if(osv != null)
				semanticError("Schema variable "+id+" already defined.");
				
				osv = SchemaVariableFactory.createModalOperatorSV(new Name(id),  
				sort, modalities);
				
				if (inSchemaMode()) {
				variables().add(osv);
				//functions().add(osv);
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
	}
	
	public final void schema_modifiers(
		SchemaVariableModifierSet mods
	) throws RecognitionException, TokenStreamException {
		
		
		ImmutableList<String> opts = null;
		
		
		try {      // for error handling
			match(LBRACKET);
			opts=simple_ident_comma_list();
			match(RBRACKET);
			if ( inputState.guessing==0 ) {
				
				final Iterator<String> it = opts.iterator ();
				while ( it.hasNext () ) {
				final String option = it.next();
				if (!mods.addModifier(option))
				semanticError(option+ 
				": Illegal or unknown modifier in declaration of schema variable");
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_19);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void pred_decl() throws RecognitionException, TokenStreamException {
		
		
		Sort[] argSorts;    
		String pred_name;
		Boolean[] whereToBind = null;
		
		
		try {      // for error handling
			pred_name=funcpred_name();
			{
			switch ( LA(1)) {
			case LBRACE:
			{
				whereToBind=where_to_bind();
				break;
			}
			case SEMI:
			case LPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			argSorts=arg_sorts(!skip_predicates);
			if ( inputState.guessing==0 ) {
				
				if (!skip_predicates) {
				
				if(whereToBind != null 
					 	   && whereToBind.length != argSorts.length) {
				semanticError("Where-to-bind list must have same length "
				+ "as argument list");
				}
				
				Function p = null;            
				
					int separatorIndex = pred_name.indexOf("::"); 
					        if (separatorIndex > 0) {
					            String sortName = pred_name.substring(0, separatorIndex);
					            String baseName = pred_name.substring(separatorIndex + 2);
						    Sort genSort = lookupSort(sortName);
						    
						    if(genSort instanceof GenericSort) {	        	            	
						    	p = SortDependingFunction.createFirstInstance(
						    	    		(GenericSort)genSort,
						    	    		new Name(baseName),
						    	    		Sort.FORMULA,
						    	    		argSorts,
						    	    		false);
						    }
					        }
				
				if(p == null) {	                        
				p = new Function(new Name(pred_name), 
						     Sort.FORMULA, 
						     argSorts,
						     whereToBind,
						     false);
				}
						if (lookup(p.name()) != null) {
						    if(!isProblemParser()) {
						        throw new AmbigiousDeclException(p.name().toString(), 
						                                         getFilename(), 
						                                         getLine(), 
						                                         getColumn());
						                                     
						    }
						}else{
				addFunction(p);         
				}
				} 
				
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_20);
			} else {
			  throw ex;
			}
		}
	}
	
	public final String  funcpred_name() throws RecognitionException, TokenStreamException {
		String result = null;
		
		
		String name = null;
		String prefix = null;
		
		
		try {      // for error handling
			boolean synPredMatched122 = false;
			if (((LA(1)==IDENT))) {
				int _m122 = mark();
				synPredMatched122 = true;
				inputState.guessing++;
				try {
					{
					sort_name();
					match(DOUBLECOLON);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched122 = false;
				}
				rewind(_m122);
inputState.guessing--;
			}
			if ( synPredMatched122 ) {
				{
				prefix=sort_name();
				match(DOUBLECOLON);
				name=simple_ident();
				if ( inputState.guessing==0 ) {
					result = prefix + "::" + name;
				}
				}
			}
			else if ((LA(1)==IDENT)) {
				{
				prefix=simple_ident();
				if ( inputState.guessing==0 ) {
					result = prefix;
				}
				}
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_21);
			} else {
			  throw ex;
			}
		}
		return result;
	}
	
	public final Boolean[]  where_to_bind() throws RecognitionException, TokenStreamException {
		Boolean[] result = null;
		
		
		List<Boolean> list = new ArrayList<Boolean>();
		
		
		try {      // for error handling
			match(LBRACE);
			{
			switch ( LA(1)) {
			case TRUE:
			{
				match(TRUE);
				if ( inputState.guessing==0 ) {
					list.add(true);
				}
				break;
			}
			case FALSE:
			{
				match(FALSE);
				if ( inputState.guessing==0 ) {
					list.add(false);
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			_loop103:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					{
					switch ( LA(1)) {
					case TRUE:
					{
						match(TRUE);
						if ( inputState.guessing==0 ) {
							list.add(true);
						}
						break;
					}
					case FALSE:
					{
						match(FALSE);
						if ( inputState.guessing==0 ) {
							list.add(false);
						}
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
				}
				else {
					break _loop103;
				}
				
			} while (true);
			}
			match(RBRACE);
			if ( inputState.guessing==0 ) {
				
				result = list.toArray(new Boolean[0]);
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_22);
			} else {
			  throw ex;
			}
		}
		return result;
	}
	
	public final Sort[]  arg_sorts(
		boolean checkSort
	) throws RecognitionException, TokenStreamException {
		Sort[] argSorts = null;
		
		
		List args = new LinkedList();
		Sort s;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				s=sortId_check(checkSort);
				if ( inputState.guessing==0 ) {
					args.add(s);
				}
				{
				_loop98:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						s=sortId_check(checkSort);
						if ( inputState.guessing==0 ) {
							args.add(s);
						}
					}
					else {
						break _loop98;
					}
					
				} while (true);
				}
				match(RPAREN);
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
			if ( inputState.guessing==0 ) {
				
				argSorts = (Sort[])args.toArray(AN_ARRAY_OF_SORTS);
				
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
		return argSorts;
	}
	
	public final int  location_ident() throws RecognitionException, TokenStreamException {
		int kind = NORMAL_NONRIGID;
		
		String id = null;
		
		try {      // for error handling
			id=simple_ident();
			if ( inputState.guessing==0 ) {
				
				if ("Location".equals(id)) {
				kind = LOCATION_MODIFIER;
				} else if (!"Location".equals(id)) {
				semanticError(
				id+": Attribute of a Non Rigid Function can only be 'Location'");        
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
		return kind;
	}
	
	public final void func_decl() throws RecognitionException, TokenStreamException {
		
		
		Sort[] argSorts;
		Boolean[] whereToBind = null;
		Sort retSort;
		String func_name;
		boolean unique = false;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case UNIQUE:
			{
				match(UNIQUE);
				if ( inputState.guessing==0 ) {
					unique=true;
				}
				break;
			}
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
			retSort=any_sortId_check(!skip_functions);
			func_name=funcpred_name();
			{
			switch ( LA(1)) {
			case LBRACE:
			{
				whereToBind=where_to_bind();
				break;
			}
			case SEMI:
			case LPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			argSorts=arg_sorts(!skip_functions);
			if ( inputState.guessing==0 ) {
				
				if (!skip_functions) {
				
					 	if(whereToBind != null 
					 	   && whereToBind.length != argSorts.length) {
				semanticError("Where-to-bind list must have same length "
				+ "as argument list");
				} 
				
				Function f = null;
				
					        int separatorIndex = func_name.indexOf("::"); 
					        if (separatorIndex > 0) {
					            String sortName = func_name.substring(0, separatorIndex);
					            String baseName = func_name.substring(separatorIndex + 2);
						    Sort genSort = lookupSort(sortName);
						    
						    if(genSort instanceof GenericSort) {	        	            	
						    	f = SortDependingFunction.createFirstInstance(
						    	    		(GenericSort)genSort,
						    	    		new Name(baseName),
						    	    		retSort,
						    	    		argSorts,
						    	    		unique);
						    }
					        }
					        
					        if(f == null) {
					            f = new Function(new Name(func_name), 
					                             retSort, 
					                             argSorts,
					                             whereToBind,
					                             unique);                    
					        }
						if (lookup(f.name()) != null) {
						    if(!isProblemParser()) {
						      throw new AmbigiousDeclException(f.name().toString(), 
						                                     getFilename(), 
						                                     getLine(), 
						                                     getColumn());
						    }
						}else{
					    	    addFunction(f);
					        }
				} 
				
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_23);
			} else {
			  throw ex;
			}
		}
	}
	
	public final KeYJavaType  arrayopid() throws RecognitionException, TokenStreamException {
		KeYJavaType componentType = null;
		
		
		try {      // for error handling
			match(EMPTYBRACKETS);
			match(LPAREN);
			componentType=keyjavatype();
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		return componentType;
	}
	
	public final Sort  sortId() throws RecognitionException, TokenStreamException {
		Sort s = null;
		
		
		try {      // for error handling
			s=sortId_check(true);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_19);
			} else {
			  throw ex;
			}
		}
		return s;
	}
	
	public final Pair<Sort,Type>  sortId_check_help(
		boolean checkSort
	) throws RecognitionException, TokenStreamException {
		Pair<Sort,Type> result = null;
		
		
		try {      // for error handling
			result=any_sortId_check_help(checkSort);
			if ( inputState.guessing==0 ) {
				
				// don't allow generic sorts or collection sorts of
				// generic sorts at this point
				Sort s = result.first;
				while ( s instanceof ArraySort ) {
					s = ((ArraySort)s).elementSort ();
				}
				
				if ( s instanceof GenericSort ) {
				throw new GenericSortException ( "sort",
				"Non-generic sort expected", s,
				getFilename (), getLine (), getColumn () );
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_24);
			} else {
			  throw ex;
			}
		}
		return result;
	}
	
	public final Sort  array_decls(
		Pair<Sort,Type> p, boolean checksort
	) throws RecognitionException, TokenStreamException {
		Sort s = null;
		
		
		int n = 0;    
		
		
		try {      // for error handling
			{
			_loop114:
			do {
				if ((LA(1)==EMPTYBRACKETS)) {
					match(EMPTYBRACKETS);
					if ( inputState.guessing==0 ) {
						n++;
					}
				}
				else {
					break _loop114;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				if (!checksort) return s;
				if(n != 0) {
				final JavaInfo ji = getJavaInfo();
				s = ArraySort.getArraySortForDim(p.first,
								 p.second, 
							         n, 
							         ji.objectSort(),
				ji.cloneableSort(), 
				ji.serializableSort());
				
				Sort last = s;
				do {
				final ArraySort as = (ArraySort) last;
				sorts().add(as);                        
				last = as.elementSort();
				} while (last instanceof ArraySort && sorts().lookup(last.name()) == null);
				} else {
				s = p.first;
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_25);
			} else {
			  throw ex;
			}
		}
		return s;
	}
	
	public final Pair<Sort,Type>  any_sortId_check_help(
		boolean checkSort
	) throws RecognitionException, TokenStreamException {
		Pair<Sort,Type> result = null;
		
		
		String name;
		
		
		try {      // for error handling
			name=simple_sort_name();
			if ( inputState.guessing==0 ) {
				
				//Special handling for byte, char, short, long:
				//these are *not* sorts, but they are nevertheless valid
				//prefixes for array sorts such as byte[], char[][][].
				//Thus, we consider them aliases for the "int" sort, and remember
				//the corresponding Java type for the case that an array sort 
				//is being declared.
				Type t = null;            
				if(name.equals(PrimitiveType.JAVA_BYTE.getName())) {
				t = PrimitiveType.JAVA_BYTE;
				name = PrimitiveType.JAVA_INT.getName();
				} else if(name.equals(PrimitiveType.JAVA_CHAR.getName())) {
				t = PrimitiveType.JAVA_CHAR;
				name = PrimitiveType.JAVA_INT.getName();            
				} else if(name.equals(PrimitiveType.JAVA_SHORT.getName())) {
				t = PrimitiveType.JAVA_SHORT;
				name = PrimitiveType.JAVA_INT.getName();
				} else if(name.equals(PrimitiveType.JAVA_INT.getName())) {
				t = PrimitiveType.JAVA_INT;
				name = PrimitiveType.JAVA_INT.getName();
				} else if(name.equals(PrimitiveType.JAVA_LONG.getName())) {
				t = PrimitiveType.JAVA_LONG;
				name = PrimitiveType.JAVA_INT.getName();
				} else if(name.equals(PrimitiveType.JAVA_BIGINT.getName())){
				t = PrimitiveType.JAVA_BIGINT;
				name = PrimitiveType.JAVA_BIGINT.getName();
				}
				
				Sort s = null;
				if(checkSort) {
				s = lookupSort(name);
				if(s == null) {
				throw new NotDeclException("sort", 
				name, 
				getFilename(), 
				getLine(),  
				getColumn()); 
				}
				}
				
				result = new Pair<Sort,Type>(s, t);
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_26);
			} else {
			  throw ex;
			}
		}
		return result;
	}
	
	public final String  simple_sort_name() throws RecognitionException, TokenStreamException {
		String name = "";
		
		String id = "";
		
		try {      // for error handling
			id=simple_ident_dots();
			if ( inputState.guessing==0 ) {
				name = id;
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_27);
			} else {
			  throw ex;
			}
		}
		return name;
	}
	
	public final String  attrid() throws RecognitionException, TokenStreamException {
		String attr = "";;
		
		
		String id = null;
		String classRef = "";
		KeYJavaType kjt = null;
		boolean brackets = false;
		
		
		try {      // for error handling
			id=simple_ident();
			{
			switch ( LA(1)) {
			case AT:
			{
				match(AT);
				match(LPAREN);
				classRef=simple_ident_dots();
				{
				switch ( LA(1)) {
				case EMPTYBRACKETS:
				{
					match(EMPTYBRACKETS);
					if ( inputState.guessing==0 ) {
						brackets = true;
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
					
					if(brackets) classRef += "[]";
					if (!isDeclParser()) {
						        kjt = getTypeByClassName(classRef);
							if(kjt == null)
					throw new NotDeclException
					("Class " + classRef + " is unknown.", 
					classRef, getFilename(), getLine(), 
					getColumn());
							classRef = kjt.getFullName();
					}
					classRef+="::";
					
				}
				break;
			}
			case EOF:
			case MODIFIES:
			case DISPLAYNAME:
			case SLASH:
			case ASSIGN:
			case DOT:
			case DOTRANGE:
			case COMMA:
			case RPAREN:
			case RBRACE:
			case LBRACKET:
			case RBRACKET:
			case PARALLEL:
			case OR:
			case AND:
			case IMP:
			case EQUALS:
			case NOT_EQUALS:
			case SEQARROW:
			case PERCENT:
			case STAR:
			case MINUS:
			case PLUS:
			case GREATER:
			case GREATEREQUAL:
			case LESS:
			case LESSEQUAL:
			case EQV:
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
				
					attr = classRef+id;
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_28);
			} else {
			  throw ex;
			}
		}
		return attr;
	}
	
	public final IdDeclaration  id_declaration() throws RecognitionException, TokenStreamException {
		 IdDeclaration idd = null ;
		
		Token  id = null;
		
		Sort s = null;
		
		
		try {      // for error handling
			id = LT(1);
			match(IDENT);
			{
			switch ( LA(1)) {
			case COLON:
			{
				match(COLON);
				s=sortId_check(true);
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
			if ( inputState.guessing==0 ) {
				
				idd = new IdDeclaration ( id.getText (), s );
				
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
		return idd;
	}
	
	public final String  sort_name() throws RecognitionException, TokenStreamException {
		String name = null;
		
		Token  brackets = null;
		
		try {      // for error handling
			name=simple_sort_name();
			{
			_loop128:
			do {
				if ((LA(1)==EMPTYBRACKETS)) {
					brackets = LT(1);
					match(EMPTYBRACKETS);
					if ( inputState.guessing==0 ) {
						name += brackets.getText();
					}
				}
				else {
					break _loop128;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_29);
			} else {
			  throw ex;
			}
		}
		return name;
	}
	
	public final Term  term() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		Term a = null;
		
		
		try {      // for error handling
			result=elementary_update_term();
			{
			_loop132:
			do {
				if ((LA(1)==PARALLEL)) {
					match(PARALLEL);
					a=elementary_update_term();
					if ( inputState.guessing==0 ) {
						
						result = tf.createTerm(UpdateJunctor.PARALLEL_UPDATE, result, a);
						
					}
				}
				else {
					break _loop132;
				}
				
			} while (true);
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final Term  elementary_update_term() throws RecognitionException, TokenStreamException {
		Term result=null;
		
		
		Term a = null;
		
		
		try {      // for error handling
			result=equivalence_term();
			{
			switch ( LA(1)) {
			case ASSIGN:
			{
				match(ASSIGN);
				a=equivalence_term();
				if ( inputState.guessing==0 ) {
					
					result = TermBuilder.DF.elementary(getServices(), result, a);
					
				}
				break;
			}
			case EOF:
			case MODIFIES:
			case DISPLAYNAME:
			case COMMA:
			case RPAREN:
			case RBRACE:
			case PARALLEL:
			case SEQARROW:
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
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final Term  equivalence_term() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		Term a1;
		
		
		try {      // for error handling
			a=implication_term();
			{
			_loop137:
			do {
				if ((LA(1)==EQV)) {
					match(EQV);
					a1=implication_term();
					if ( inputState.guessing==0 ) {
						a = tf.createTerm(Equality.EQV, new Term[]{a, a1});
					}
				}
				else {
					break _loop137;
				}
				
			} while (true);
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  implication_term() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		Term a1;
		
		
		try {      // for error handling
			a=disjunction_term();
			{
			switch ( LA(1)) {
			case IMP:
			{
				match(IMP);
				a1=implication_term();
				if ( inputState.guessing==0 ) {
					a = tf.createTerm(Junctor.IMP, new Term[]{a, a1});
				}
				break;
			}
			case EOF:
			case MODIFIES:
			case DISPLAYNAME:
			case ASSIGN:
			case COMMA:
			case RPAREN:
			case RBRACE:
			case PARALLEL:
			case SEQARROW:
			case EQV:
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
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  disjunction_term() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		Term a1;
		
		
		try {      // for error handling
			a=conjunction_term();
			{
			_loop142:
			do {
				if ((LA(1)==OR)) {
					match(OR);
					a1=conjunction_term();
					if ( inputState.guessing==0 ) {
						a = tf.createTerm(Junctor.OR, new Term[]{a, a1});
					}
				}
				else {
					break _loop142;
				}
				
			} while (true);
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  conjunction_term() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		Term a1;
		
		
		try {      // for error handling
			a=term60();
			{
			_loop145:
			do {
				if ((LA(1)==AND)) {
					match(AND);
					a1=term60();
					if ( inputState.guessing==0 ) {
						a = tf.createTerm(Junctor.AND, new Term[]{a, a1});
					}
				}
				else {
					break _loop145;
				}
				
			} while (true);
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  term60() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case NOT:
			case FORALL:
			case EXISTS:
			case MODALITY:
			{
				a=unary_formula();
				break;
			}
			case IF:
			case IFEX:
			case TRUE:
			case FALSE:
			case LPAREN:
			case LBRACE:
			case AT:
			case MINUS:
			case STRING_LITERAL:
			case CHAR_LITERAL:
			case IDENT:
			case NUM_LITERAL:
			{
				a=equality_term();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  unary_formula() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		Term a1;
		
		try {      // for error handling
			switch ( LA(1)) {
			case NOT:
			{
				match(NOT);
				a1=term60();
				if ( inputState.guessing==0 ) {
					a = tf.createTerm(Junctor.NOT,new Term[]{a1});
				}
				break;
			}
			case FORALL:
			case EXISTS:
			{
				a=quantifierterm();
				break;
			}
			case MODALITY:
			{
				a=modality_dl_term();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  equality_term() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		Term a1;
		boolean negated = false;
		
		
		try {      // for error handling
			a=logicTermReEntry();
			{
			switch ( LA(1)) {
			case EQUALS:
			case NOT_EQUALS:
			{
				{
				switch ( LA(1)) {
				case EQUALS:
				{
					match(EQUALS);
					break;
				}
				case NOT_EQUALS:
				{
					match(NOT_EQUALS);
					if ( inputState.guessing==0 ) {
						negated = true;
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				a1=logicTermReEntry();
				if ( inputState.guessing==0 ) {
					
					if (a.sort() == Sort.FORMULA ||
					a1.sort() == Sort.FORMULA) {
					String errorMessage = 
					"The term equality \'=\'/\'!=\' is not "+
					"allowed between formulas.\n Please use \'" + Equality.EQV +
					"\' in combination with \'" + Junctor.NOT + "\' instead.";
					if (a.op() == Junctor.TRUE || a.op() == Junctor.FALSE ||
					a1.op() == Junctor.TRUE || a1.op() == Junctor.FALSE) {
					errorMessage += 
					" It seems as if you have mixed up the boolean " +
					"constants \'TRUE\'/\'FALSE\' " +
					"with the formulas \'true\'/\'false\'.";
					}
					semanticError(errorMessage);
					}
					a = tf.createTerm(Equality.EQUALS, a, a1);
					
					if (negated) {
					a = tf.createTerm(Junctor.NOT, a);
					}
					
				}
				break;
			}
			case EOF:
			case MODIFIES:
			case DISPLAYNAME:
			case ASSIGN:
			case COMMA:
			case RPAREN:
			case RBRACE:
			case PARALLEL:
			case OR:
			case AND:
			case IMP:
			case SEQARROW:
			case EQV:
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
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  quantifierterm() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		Operator op = null;
		ImmutableList<QuantifiableVariable> vs = null;
		Term a1 = null;
		Namespace orig = variables();  
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case FORALL:
			{
				match(FORALL);
				if ( inputState.guessing==0 ) {
					op = Quantifier.ALL;
				}
				break;
			}
			case EXISTS:
			{
				match(EXISTS);
				if ( inputState.guessing==0 ) {
					op = Quantifier.EX;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			vs=bound_variables();
			a1=term60();
			if ( inputState.guessing==0 ) {
				
				a = tf.createTerm((Quantifier)op,
				new ImmutableArray<Term>(a1),
					       		      new ImmutableArray<QuantifiableVariable>(vs.toArray(new QuantifiableVariable[vs.size()])),
					       		      null);
				if(!isGlobalDeclTermParser())
				unbindVars(orig);
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_30);
			} else {
			  throw ex;
			}
		}
		return a;
	}
	
	public final Term  modality_dl_term() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		Token  modality = null;
		
		Term a1;
		Term[] args = null;
		Term[] terms = null;
		Operator op = null;
		PairOfStringAndJavaBlock sjb = null;
		
		
		try {      // for error handling
			modality = LT(1);
			match(MODALITY);
			if ( inputState.guessing==0 ) {
				
				sjb=getJavaBlock(modality);
				Debug.out("op: ", sjb.opName);
				Debug.out("program: ", sjb.javaBlock);
				if(sjb.opName.charAt(0) == '#') {
				if (!inSchemaMode()) {
				semanticError
				("No schema elements allowed outside taclet declarations ("+sjb.opName+")");
				}
				op = (SchemaVariable)variables().lookup(new Name(sjb.opName));
				} else {
				op = Modality.getModality(sjb.opName);
				}
				if(op == null) {
				semanticError("Unknown modal operator: "+sjb.opName);
				}
				
			}
			{
			if (!(op != null && op.arity() == 1))
			  throw new SemanticException("op != null && op.arity() == 1");
			a1=term60();
			if ( inputState.guessing==0 ) {
				
				a = tf.createTerm(op, new Term[]{a1}, null, sjb.javaBlock);
				
			}
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  logicTermReEntry() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		Term a1 = null;
		Function op = null;
		
		
		try {      // for error handling
			a=weak_arith_op_term();
			{
			switch ( LA(1)) {
			case GREATER:
			case GREATEREQUAL:
			case LESS:
			case LESSEQUAL:
			{
				op=relation_op();
				a1=weak_arith_op_term();
				if ( inputState.guessing==0 ) {
					
					a = tf.createTerm(op, a, a1);
					
				}
				break;
			}
			case EOF:
			case MODIFIES:
			case DISPLAYNAME:
			case ASSIGN:
			case DOTRANGE:
			case COMMA:
			case RPAREN:
			case RBRACE:
			case RBRACKET:
			case PARALLEL:
			case OR:
			case AND:
			case IMP:
			case EQUALS:
			case NOT_EQUALS:
			case SEQARROW:
			case EQV:
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
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Function  relation_op() throws RecognitionException, TokenStreamException {
		Function op = null;
		
		
		String op_name = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LESS:
			{
				match(LESS);
				if ( inputState.guessing==0 ) {
					op_name = "lt";
				}
				break;
			}
			case LESSEQUAL:
			{
				match(LESSEQUAL);
				if ( inputState.guessing==0 ) {
					op_name = "leq";
				}
				break;
			}
			case GREATER:
			{
				match(GREATER);
				if ( inputState.guessing==0 ) {
					op_name = "gt";
				}
				break;
			}
			case GREATEREQUAL:
			{
				match(GREATEREQUAL);
				if ( inputState.guessing==0 ) {
					op_name = "geq";
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
				
				op = (Function) functions().lookup(new Name(op_name)); 
				if(op == null) {
				semanticError("Function symbol '"+op_name+"' not found.");
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_31);
			} else {
			  throw ex;
			}
		}
		return op;
	}
	
	public final Function  weak_arith_op() throws RecognitionException, TokenStreamException {
		Function op = null;
		
		
		String op_name = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case PLUS:
			{
				match(PLUS);
				if ( inputState.guessing==0 ) {
					op_name = "add";
				}
				break;
			}
			case MINUS:
			{
				match(MINUS);
				if ( inputState.guessing==0 ) {
					op_name = "sub";
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
				
				op = (Function) functions().lookup(new Name(op_name)); 
				if(op == null) {
				semanticError("Function symbol '"+op_name+"' not found.");
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_31);
			} else {
			  throw ex;
			}
		}
		return op;
	}
	
	public final Function  strong_arith_op() throws RecognitionException, TokenStreamException {
		Function op = null;
		
		
		String op_name = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case STAR:
			{
				match(STAR);
				if ( inputState.guessing==0 ) {
					op_name = "mul";
				}
				break;
			}
			case SLASH:
			{
				match(SLASH);
				if ( inputState.guessing==0 ) {
					op_name = "div";
				}
				break;
			}
			case PERCENT:
			{
				match(PERCENT);
				if ( inputState.guessing==0 ) {
					op_name = "mod";
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
				
				op = (Function) functions().lookup(new Name(op_name)); 
				if(op == null) {
				semanticError("Function symbol '"+op_name+"' not found.");
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_31);
			} else {
			  throw ex;
			}
		}
		return op;
	}
	
	public final Term  weak_arith_op_term() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		Term a1 = null;
		Function op = null;
		
		
		try {      // for error handling
			a=strong_arith_op_term();
			{
			_loop163:
			do {
				if ((LA(1)==MINUS||LA(1)==PLUS)) {
					op=weak_arith_op();
					a1=strong_arith_op_term();
					if ( inputState.guessing==0 ) {
						
						a = tf.createTerm(op, a, a1);
						
					}
				}
				else {
					break _loop163;
				}
				
			} while (true);
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  strong_arith_op_term() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		
		Term a1 = null;
		Function op = null;
		
		
		try {      // for error handling
			a=term110();
			{
			_loop166:
			do {
				if ((LA(1)==SLASH||LA(1)==PERCENT||LA(1)==STAR)) {
					op=strong_arith_op();
					a1=term110();
					if ( inputState.guessing==0 ) {
						
						a = tf.createTerm(op, a, a1);
						
					}
				}
				else {
					break _loop166;
				}
				
			} while (true);
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
/**
 * helps to better distinguish if formulas are allowed or only term are
 * accepted
 * WATCHOUT: Woj: the check for Sort.FORMULA had to be removed to allow
 * infix operators and the whole bunch of grammar rules above.
 */
	public final Term  term110() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case IF:
			case IFEX:
			case TRUE:
			case FALSE:
			case LPAREN:
			case AT:
			case MINUS:
			case STRING_LITERAL:
			case CHAR_LITERAL:
			case IDENT:
			case NUM_LITERAL:
			{
				result=accessterm();
				break;
			}
			case LBRACE:
			{
				result=update_or_substitution();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
					/*
				if (result.sort() == Sort.FORMULA) {
				semanticError("Only terms may stand here.");
				}
					*/
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_32);
			} else {
			  throw ex;
			}
		}
		return result;
	}
	
	public final Term  accessterm() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		Sort s = null;
		
		
		try {      // for error handling
			boolean synPredMatched185 = false;
			if (((LA(1)==MINUS))) {
				int _m185 = mark();
				synPredMatched185 = true;
				inputState.guessing++;
				try {
					{
					match(MINUS);
					matchNot(NUM_LITERAL);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched185 = false;
				}
				rewind(_m185);
inputState.guessing--;
			}
			if ( synPredMatched185 ) {
				match(MINUS);
				result=term110();
				if ( inputState.guessing==0 ) {
					
					if (result.sort() != Sort.FORMULA) {
					result = tf.createTerm
					((Function) functions().lookup(new Name("neg")), result);
					} else {
					semanticError("Formula cannot be prefixed with '-'");
					}
					
				}
			}
			else {
				boolean synPredMatched187 = false;
				if (((LA(1)==LPAREN))) {
					int _m187 = mark();
					synPredMatched187 = true;
					inputState.guessing++;
					try {
						{
						match(LPAREN);
						any_sortId_check(false);
						match(RPAREN);
						term110();
						}
					}
					catch (RecognitionException pe) {
						synPredMatched187 = false;
					}
					rewind(_m187);
inputState.guessing--;
				}
				if ( synPredMatched187 ) {
					match(LPAREN);
					s=any_sortId_check(true);
					match(RPAREN);
					result=term110();
					if ( inputState.guessing==0 ) {
						
						final Sort objectSort = getServices().getJavaInfo().objectSort();
						if(s==null) {
						semanticError("Tried to cast to unknown type.");
						} else if (objectSort != null
						&& !s.extendsTrans(objectSort) 
						&& result.sort().extendsTrans(objectSort)) {
						semanticError("Illegal cast from " + result.sort() + 
						" to sort " + s +
						". Casts between primitive and reference types are not allowed. ");
						}
						result = tf.createTerm(s.getCastSymbol(getServices()), result);
							
					}
				}
				else if ((_tokenSet_33.member(LA(1)))) {
					{
					if (((LA(1)==IDENT))&&(isStaticQuery())) {
						result=static_query();
					}
					else if (((LA(1)==IDENT))&&(isStaticAttribute())) {
						result=static_attribute_suffix();
					}
					else if ((_tokenSet_33.member(LA(1)))) {
						result=atom();
					}
					else {
						throw new NoViableAltException(LT(1), getFilename());
					}
					
					}
					{
					_loop190:
					do {
						switch ( LA(1)) {
						case LBRACKET:
						{
							result=array_access_suffix(result);
							break;
						}
						case DOT:
						{
							result=attribute_or_query_suffix(result);
							break;
						}
						default:
						{
							break _loop190;
						}
						}
					} while (true);
					}
				}
				else {
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
			}
			catch (TermCreationException ex) {
				if (inputState.guessing==0) {
					
					semanticError(ex.getMessage());
					
				} else {
					throw ex;
				}
			}
			return result;
		}
		
	public final Term  update_or_substitution() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		try {      // for error handling
			boolean synPredMatched221 = false;
			if (((LA(1)==LBRACE))) {
				int _m221 = mark();
				synPredMatched221 = true;
				inputState.guessing++;
				try {
					{
					match(LBRACE);
					match(SUBST);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched221 = false;
				}
				rewind(_m221);
inputState.guessing--;
			}
			if ( synPredMatched221 ) {
				result=substitutionterm();
			}
			else if ((LA(1)==LBRACE)) {
				result=updateterm();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_32);
			} else {
			  throw ex;
			}
		}
		return result;
	}
	
	public final String  staticAttributeOrQueryReference() throws RecognitionException, TokenStreamException {
		String attrReference = "";
		
		Token  id = null;
		
		try {      // for error handling
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				
				attrReference = id.getText(); 
				while (isPackage(attrReference) || LA(2)==NUM_LITERAL || 
				(LT(2).getText().charAt(0)<='Z' && LT(2).getText().charAt(0)>='A' && 
					    		(LT(2).getText().length()==1 || LT(2).getText().charAt(1)<='z' && LT(2).getText().charAt(1)>='a')) &&
				LA(1) == DOT) {
				if(getTypeByClassName(attrReference)!=null){
				ProgramVariable maybeAttr = 
				getJavaInfo().getAttribute(LT(2).getText(), getTypeByClassName(attrReference));
				if(maybeAttr!=null){
				break;
				}
				}
				
				match(DOT);
				attrReference += "." + LT(1).getText();
				if(LA(1)==NUM_LITERAL){
					match(NUM_LITERAL);
				}else{
					 	match(IDENT);
				}
				}      
				
			}
			{
			_loop171:
			do {
				if ((LA(1)==EMPTYBRACKETS)) {
					match(EMPTYBRACKETS);
					if ( inputState.guessing==0 ) {
						attrReference += "[]";
					}
				}
				else {
					break _loop171;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				KeYJavaType kjt = null;
				kjt = getTypeByClassName(attrReference);
				if (kjt == null) {
				throw new NotDeclException
				("Class " + attrReference + " is unknown.", 
				attrReference, getFilename(), getLine(), 
				getColumn());
				}	        
				attrReference = kjt.getSort().name().toString();            
				match(DOT);
				attrReference += "::" + LT(1).getText();
				match(IDENT);
					    if(savedGuessing > -1) {
					      inputState.guessing = savedGuessing;
					      savedGuessing = -1;
					    }
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_34);
			} else {
			  throw ex;
			}
		}
		return attrReference;
	}
	
	public final Term  static_attribute_suffix() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		Operator v = null;
		String attributeName = "";
		
		
		try {      // for error handling
			attributeName=staticAttributeOrQueryReference();
			if ( inputState.guessing==0 ) {
				
					String className;
				if(attributeName.indexOf(':')!=-1){	
					       		className = 
						   			attributeName.substring(0, attributeName.indexOf(':'));
				}else{
						className = 
						   			attributeName.substring(0, attributeName.lastIndexOf("."));	
				}	
					       	v = getAttribute(getTypeByClassName(className).getSort(), attributeName); 
					
			}
			if ( inputState.guessing==0 ) {
				result = createAttributeTerm(null, v);
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final Term  attribute_or_query_suffix(
		Term prefix
	) throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		Operator v = null;
		result = prefix;
		String attributeName = "";    
		
		
		try {      // for error handling
			match(DOT);
			{
			boolean synPredMatched177 = false;
			if (((LA(1)==IDENT))) {
				int _m177 = mark();
				synPredMatched177 = true;
				inputState.guessing++;
				try {
					{
					match(IDENT);
					{
					switch ( LA(1)) {
					case AT:
					{
						match(AT);
						match(LPAREN);
						simple_ident_dots();
						match(RPAREN);
						break;
					}
					case LPAREN:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					match(LPAREN);
					}
				}
				catch (RecognitionException pe) {
					synPredMatched177 = false;
				}
				rewind(_m177);
inputState.guessing--;
			}
			if ( synPredMatched177 ) {
				{
				result=query(prefix);
				}
			}
			else if ((LA(1)==IDENT)) {
				attributeName=attrid();
				if ( inputState.guessing==0 ) {
					
					v = getAttribute(prefix.sort(), attributeName);
						      result = createAttributeTerm(prefix, v);
					
				}
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final Term  query(
		Term prefix
	) throws RecognitionException, TokenStreamException {
		Term result = null;
		
		Token  mid = null;
		
		String classRef = "";
		Term[] args = null; 
		boolean brackets = false;
		
		
		try {      // for error handling
			mid = LT(1);
			match(IDENT);
			{
			switch ( LA(1)) {
			case AT:
			{
				match(AT);
				match(LPAREN);
				classRef=simple_ident_dots();
				{
				switch ( LA(1)) {
				case EMPTYBRACKETS:
				{
					match(EMPTYBRACKETS);
					if ( inputState.guessing==0 ) {
						brackets = true;
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
				break;
			}
			case LPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			args=argument_list();
			if ( inputState.guessing==0 ) {
				
				if("".equals(classRef)){
				classRef = prefix.sort().name().toString();
				}else{
				if(brackets) classRef += "[]";
				KeYJavaType kjt = getTypeByClassName(classRef);
				if(kjt == null)
				throw new NotDeclException
				("Class " + classRef + " is unknown.", 
				classRef, getFilename(), getLine(), 
				getColumn());
				classRef = kjt.getFullName();
				}
				result = getServices().getJavaInfo().getProgramMethodTerm
				(prefix, mid.getText(), args, classRef);
				
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(),getColumn()));
				
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final Term[]  argument_list() throws RecognitionException, TokenStreamException {
		Term[] result = null;
		
		
		List<Term> args = new LinkedList<Term>();
		Term p1, p2;
		
		
		try {      // for error handling
			match(LPAREN);
			{
			switch ( LA(1)) {
			case NOT:
			case FORALL:
			case EXISTS:
			case IF:
			case IFEX:
			case TRUE:
			case FALSE:
			case LPAREN:
			case LBRACE:
			case AT:
			case MINUS:
			case STRING_LITERAL:
			case CHAR_LITERAL:
			case IDENT:
			case NUM_LITERAL:
			case MODALITY:
			{
				p1=argument();
				if ( inputState.guessing==0 ) {
					args.add(p1);
				}
				{
				_loop238:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						p2=argument();
						if ( inputState.guessing==0 ) {
							args.add(p2);
						}
					}
					else {
						break _loop238;
					}
					
				} while (true);
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
				
				result = args.toArray(new Term[0]);
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_35);
			} else {
			  throw ex;
			}
		}
		return result;
	}
	
	public final Term  static_query() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		String queryRef = "";
		Term[] args = null;
		Operator ts = null;
		
		
		try {      // for error handling
			queryRef=staticAttributeOrQueryReference();
			args=argument_list();
			if ( inputState.guessing==0 ) {
				
				int index = queryRef.indexOf(':');
				String className = queryRef.substring(0, index); 
				String qname = queryRef.substring(index+2); 
				result = getServices().getJavaInfo().getProgramMethodTerm(null, qname, args, className);
				if(result == null && isTermParser()) {
					  final Sort sort = lookupSort(className);
				if (sort == null) {
						semanticError("Could not find matching sort for " + className);
				}
				KeYJavaType kjt = getServices().getJavaInfo().getKeYJavaType(sort);
				if (kjt == null) {
						semanticError("Found logic sort for " + className + 
						 " but no corresponding java type!");
				}          
				}
					    
				
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(),getColumn()));
				
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final Term  atom() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		Token  literal = null;
		
		ImmutableArray<ITermLabel> labels;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				a=term();
				match(RPAREN);
				break;
			}
			case TRUE:
			{
				match(TRUE);
				if ( inputState.guessing==0 ) {
					a = tf.createTerm(Junctor.TRUE);
				}
				break;
			}
			case FALSE:
			{
				match(FALSE);
				if ( inputState.guessing==0 ) {
					a = tf.createTerm(Junctor.FALSE);
				}
				break;
			}
			case IF:
			{
				a=ifThenElseTerm();
				break;
			}
			case IFEX:
			{
				a=ifExThenElseTerm();
				break;
			}
			case STRING_LITERAL:
			{
				literal = LT(1);
				match(STRING_LITERAL);
				if ( inputState.guessing==0 ) {
					
					a = getServices().getTypeConverter().convertToLogicElement(new de.uka.ilkd.key.java.expression.literal.StringLiteral(literal.getText()));
					
				}
				break;
			}
			default:
				if (((LA(1)==IDENT))&&(isTermTransformer())) {
					a=specialTerm();
				}
				else if ((_tokenSet_36.member(LA(1)))) {
					a=funcpredvarterm();
				}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			{
			switch ( LA(1)) {
			case LGUILLEMETS:
			{
				match(LGUILLEMETS);
				labels=label();
				if ( inputState.guessing==0 ) {
					if (labels.size() > 0) {a = TermBuilder.DF.label(a, labels);}
				}
				match(RGUILLEMETS);
				break;
			}
			case EOF:
			case MODIFIES:
			case DISPLAYNAME:
			case SLASH:
			case ASSIGN:
			case DOT:
			case DOTRANGE:
			case COMMA:
			case RPAREN:
			case RBRACE:
			case LBRACKET:
			case RBRACKET:
			case PARALLEL:
			case OR:
			case AND:
			case IMP:
			case EQUALS:
			case NOT_EQUALS:
			case SEQARROW:
			case PERCENT:
			case STAR:
			case MINUS:
			case PLUS:
			case GREATER:
			case GREATEREQUAL:
			case LESS:
			case LESSEQUAL:
			case EQV:
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
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  array_access_suffix(
		Term arrayReference
	) throws RecognitionException, TokenStreamException {
		Term result = arrayReference;
		
		
		Term indexTerm  = null;
		Term rangeFrom = null;
		Term rangeTo   = null;     
		
		
		try {      // for error handling
			match(LBRACKET);
			{
			switch ( LA(1)) {
			case STAR:
			{
				match(STAR);
				if ( inputState.guessing==0 ) {
					
						rangeFrom = toZNotation("0", functions());
						Term lt = TermBuilder.DF.dotLength(getServices(), arrayReference);
						Term one = toZNotation("1", functions());
						   		rangeTo = tf.createTerm
							((Function) functions().lookup(new Name("sub")), lt, one); 
					
				}
				break;
			}
			case IF:
			case IFEX:
			case TRUE:
			case FALSE:
			case LPAREN:
			case LBRACE:
			case AT:
			case MINUS:
			case STRING_LITERAL:
			case CHAR_LITERAL:
			case IDENT:
			case NUM_LITERAL:
			{
				indexTerm=logicTermReEntry();
				{
				switch ( LA(1)) {
				case DOTRANGE:
				{
					match(DOTRANGE);
					rangeTo=logicTermReEntry();
					if ( inputState.guessing==0 ) {
						rangeFrom = indexTerm;
					}
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
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RBRACKET);
			if ( inputState.guessing==0 ) {
				
					if(rangeTo != null) {
						if(quantifiedArrayGuard == null) {
							semanticError(
						  	"Quantified array expressions are only allowed in locations.");
						}
						LogicVariable indexVar = new LogicVariable(new Name("i"), 
						   	   		   (Sort) sorts().lookup(new Name("int")));
						indexTerm = tf.createTerm(indexVar);
						   	
						Function leq = (Function) functions().lookup(new Name("leq"));
						Term fromTerm = tf.createTerm(leq, rangeFrom, indexTerm);
						Term toTerm = tf.createTerm(leq, indexTerm, rangeTo);
						Term guardTerm = tf.createTerm(Junctor.AND, fromTerm, toTerm);
						quantifiedArrayGuard = tf.createTerm(Junctor.AND, quantifiedArrayGuard, guardTerm);
						}
				result = TermBuilder.DF.dotArr(getServices(), result, indexTerm); 
				
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				semanticError(ex.getMessage());
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final HashSet  accesstermlist() throws RecognitionException, TokenStreamException {
		HashSet accessTerms = new HashSet();
		
		Term t = null;
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case IF:
			case IFEX:
			case TRUE:
			case FALSE:
			case LPAREN:
			case AT:
			case MINUS:
			case STRING_LITERAL:
			case CHAR_LITERAL:
			case IDENT:
			case NUM_LITERAL:
			{
				t=accessterm();
				if ( inputState.guessing==0 ) {
					accessTerms.add(t);
				}
				{
				_loop199:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						t=accessterm();
						if ( inputState.guessing==0 ) {
							accessTerms.add(t);
						}
					}
					else {
						break _loop199;
					}
					
				} while (true);
				}
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
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		return accessTerms;
	}
	
	public final Term  specialTerm() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		Operator vf = null;
		
		
		try {      // for error handling
			if (!(isTacletParser() || isProblemParser()))
			  throw new SemanticException("isTacletParser() || isProblemParser()");
			result=metaTerm();
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final Term  funcpredvarterm() throws RecognitionException, TokenStreamException {
		Term a = null;
		
		Token  ch = null;
		Token  number = null;
		
		ImmutableList<QuantifiableVariable> boundVars = null;
		Term[] args = null;
		String varfuncid;
		String neg = "";
		boolean opSV = false;
		Namespace orig = variables();
		boolean limited = false;  
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case CHAR_LITERAL:
			{
				ch = LT(1);
				match(CHAR_LITERAL);
				if ( inputState.guessing==0 ) {
					
					String s = ch.getText();
					int intVal = 0;
					if (s.length()==3) {
					intVal = (int)s.charAt(1);
					} else {
					try {
					intVal = Integer.parseInt(s.substring(3,s.length()-1),16);
					} catch (NumberFormatException ex) {
					semanticError("'"+s+"' is not a valid character.");
					}       
					}
					a = tf.createTerm((Function) functions().lookup(new Name("C")), 
					toZNotation(""+intVal, functions()).sub(0));
					
				}
				break;
			}
			case MINUS:
			case NUM_LITERAL:
			{
				{
				switch ( LA(1)) {
				case MINUS:
				{
					match(MINUS);
					if ( inputState.guessing==0 ) {
						neg = "-";
					}
					break;
				}
				case NUM_LITERAL:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				number = LT(1);
				match(NUM_LITERAL);
				if ( inputState.guessing==0 ) {
					a = toZNotation(neg+number.getText(), functions());
				}
				break;
			}
			case AT:
			{
				match(AT);
				a=abbreviation();
				break;
			}
			case IDENT:
			{
				varfuncid=funcpred_name();
				{
				switch ( LA(1)) {
				case LIMITED:
				{
					match(LIMITED);
					if ( inputState.guessing==0 ) {
						limited = true;
					}
					break;
				}
				case EOF:
				case MODIFIES:
				case DISPLAYNAME:
				case SLASH:
				case ASSIGN:
				case DOT:
				case DOTRANGE:
				case COMMA:
				case LPAREN:
				case RPAREN:
				case LBRACE:
				case RBRACE:
				case LBRACKET:
				case RBRACKET:
				case PARALLEL:
				case OR:
				case AND:
				case IMP:
				case EQUALS:
				case NOT_EQUALS:
				case SEQARROW:
				case PERCENT:
				case STAR:
				case MINUS:
				case PLUS:
				case GREATER:
				case GREATEREQUAL:
				case LESS:
				case LESSEQUAL:
				case LGUILLEMETS:
				case EQV:
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
				case LBRACE:
				{
					{
					match(LBRACE);
					boundVars=bound_variables();
					match(RBRACE);
					args=argument_list();
					}
					break;
				}
				case LPAREN:
				{
					args=argument_list();
					break;
				}
				case EOF:
				case MODIFIES:
				case DISPLAYNAME:
				case SLASH:
				case ASSIGN:
				case DOT:
				case DOTRANGE:
				case COMMA:
				case RPAREN:
				case RBRACE:
				case LBRACKET:
				case RBRACKET:
				case PARALLEL:
				case OR:
				case AND:
				case IMP:
				case EQUALS:
				case NOT_EQUALS:
				case SEQARROW:
				case PERCENT:
				case STAR:
				case MINUS:
				case PLUS:
				case GREATER:
				case GREATEREQUAL:
				case LESS:
				case LESSEQUAL:
				case LGUILLEMETS:
				case EQV:
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
					
					if(varfuncid.equals("inReachableState") && args == null) {
						        a = TermBuilder.DF.wellFormed(getServices().getTypeConverter().getHeapLDT().getHeap(), getServices());
						    } else if(varfuncid.equals("skip") && args == null) {
						        a = tf.createTerm(UpdateJunctor.SKIP);
						    } else {
						            Operator op = lookupVarfuncId(varfuncid, args);  
						            if(limited) {
						                if(op.getClass() == ObserverFunction.class) {
						                    op = getServices().getSpecificationRepository()
						                                      .limitObs((ObserverFunction)op).first;
						                } else {
						                    semanticError("Cannot can be limited: " + op);
						                }
						            }   
						                   
						            if (op instanceof ParsableVariable) {
						                a = termForParsedVariable((ParsableVariable)op);
						            } else {
						                if (args==null) {
						                    args = new Term[0];
						                }
						
						                if(boundVars == null) {
						                    a = tf.createTerm(op, args);
						                } else {
						                    //sanity check
						                    assert op instanceof Function;
						                    for(int i = 0; i < args.length; i++) {
						                        if(i < op.arity() && !op.bindVarsAt(i)) {
						                            for(QuantifiableVariable qv : args[i].freeVars()) {
						                                if(boundVars.contains(qv)) {
						                                    semanticError("Building function term "+op+" with bound variables failed: "
						                                                   + "Variable " + qv + " must not occur free in subterm " + args[i]);
						                                } 
						                            }	                            
						                        }
						                    }
						                    
						                    //create term
						                    a = tf.createTerm(op, args, new ImmutableArray<QuantifiableVariable>(boundVars.toArray(new QuantifiableVariable[boundVars.size()])), null);
						                }
						            }
						    }
						    
						    if(boundVars != null) {
						        unbindVars(orig);
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
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return a;
	}
	
	public final Term  ifThenElseTerm() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		Term condF, thenT, elseT;
		
		
		try {      // for error handling
			match(IF);
			match(LPAREN);
			condF=term();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				if (condF.sort() != Sort.FORMULA) {
				semanticError
						  ("Condition of an \\if-then-else term has to be a formula.");
				}
				
			}
			match(THEN);
			match(LPAREN);
			thenT=term();
			match(RPAREN);
			match(ELSE);
			match(LPAREN);
			elseT=term();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				result = tf.createTerm ( IfThenElse.IF_THEN_ELSE, new Term[]{condF, thenT, elseT} );
				
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final Term  ifExThenElseTerm() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		ImmutableList<QuantifiableVariable> exVars 
			= ImmutableSLList.<QuantifiableVariable>nil();
		Term condF, thenT, elseT;
		Namespace orig = variables();
		
		
		try {      // for error handling
			match(IFEX);
			exVars=bound_variables();
			match(LPAREN);
			condF=term();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				if (condF.sort() != Sort.FORMULA) {
				semanticError
						  ("Condition of an \\ifEx-then-else term has to be a formula.");
				}
				
			}
			match(THEN);
			match(LPAREN);
			thenT=term();
			match(RPAREN);
			match(ELSE);
			match(LPAREN);
			elseT=term();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				ImmutableArray<QuantifiableVariable> exVarsArray
					= new ImmutableArray<QuantifiableVariable>( 
					     exVars.toArray(new QuantifiableVariable[exVars.size()]));
				result = tf.createTerm ( IfExThenElse.IF_EX_THEN_ELSE,  
				new Term[]{condF, thenT, elseT}, 
				exVarsArray, 
				null );
				if(!isGlobalDeclTermParser()) {
				unbindVars(orig);
				}
				
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final ImmutableArray<ITermLabel>  label() throws RecognitionException, TokenStreamException {
		ImmutableArray<ITermLabel> labels = new ImmutableArray<ITermLabel>();
		
		
		ArrayList<ITermLabel> labelList = new ArrayList<ITermLabel>();
		ITermLabel label;
		
		
		try {      // for error handling
			label=single_label();
			if ( inputState.guessing==0 ) {
				labelList.add(label);
			}
			{
			_loop205:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					label=single_label();
					if ( inputState.guessing==0 ) {
						labelList.add(label);
					}
				}
				else {
					break _loop205;
				}
				
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
					labels = new ImmutableArray<ITermLabel>((ITermLabel[])labelList.toArray(new ITermLabel[labelList.size()]));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_37);
			} else {
			  throw ex;
			}
		}
		return labels;
	}
	
	public final ITermLabel  single_label() throws RecognitionException, TokenStreamException {
		ITermLabel label=null;
		
		Token  name = null;
		Token  star = null;
		Token  param1 = null;
		Token  param2 = null;
		
		String labelName = "";
		ITermLabel left = null;
		ITermLabel right = null;
		List<String> parameters = new LinkedList<String>();
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case IDENT:
			{
				name = LT(1);
				match(IDENT);
				if ( inputState.guessing==0 ) {
					labelName=name.getText();
				}
				break;
			}
			case STAR:
			{
				star = LT(1);
				match(STAR);
				if ( inputState.guessing==0 ) {
					labelName=star.getText();
				}
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
			case LPAREN:
			{
				match(LPAREN);
				param1 = LT(1);
				match(STRING_LITERAL);
				if ( inputState.guessing==0 ) {
					parameters.add(param1.getText().substring(1,param1.getText().length()-1));
				}
				{
				_loop210:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						param2 = LT(1);
						match(STRING_LITERAL);
						if ( inputState.guessing==0 ) {
							parameters.add(param2.getText().substring(1,param2.getText().length()-1));
						}
					}
					else {
						break _loop210;
					}
					
				} while (true);
				}
				match(RPAREN);
				break;
			}
			case COMMA:
			case RGUILLEMETS:
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
				
					label = LabelFactory.createLabel(labelName, parameters);
				
			}
		}
		catch (UnknownLabelException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return label;
	}
	
	public final Term  abbreviation() throws RecognitionException, TokenStreamException {
		Term a=null;
		
		
		String sc = null;
		
		
		try {      // for error handling
			{
			sc=simple_ident();
			if ( inputState.guessing==0 ) {
				
				a =  scm.getTerm(sc);
				if(a==null){
				throw new NotDeclException
				("abbreviation", sc, 
				getFilename(), getLine(), getColumn());
				}                                
				
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_35);
			} else {
			  throw ex;
			}
		}
		return a;
	}
	
	public final ImmutableList<QuantifiableVariable>  bound_variables() throws RecognitionException, TokenStreamException {
		ImmutableList<QuantifiableVariable> list = ImmutableSLList.<QuantifiableVariable>nil();
		
		
		QuantifiableVariable var = null;
		
		
		try {      // for error handling
			var=one_bound_variable();
			if ( inputState.guessing==0 ) {
				list = list.append(var);
			}
			{
			_loop228:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					var=one_bound_variable();
					if ( inputState.guessing==0 ) {
						list = list.append(var);
					}
				}
				else {
					break _loop228;
				}
				
			} while (true);
			}
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_38);
			} else {
			  throw ex;
			}
		}
		return list;
	}
	
	public final Term  argument() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		ImmutableArray<QuantifiableVariable> vars = null;
		Term a;
		
		
		try {      // for error handling
			{
			if (((_tokenSet_39.member(LA(1))))&&(isTermParser() || isGlobalDeclTermParser())) {
				result=term();
			}
			else if ((_tokenSet_39.member(LA(1)))) {
				result=term60();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		return result;
	}
	
	public final Term  substitutionterm() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		QuantifiableVariable v = null;
		SubstOp op = WarySubstOp.SUBST;
		Term a1 = null;
		Term a2 = null;
		Namespace orig = variables();  
		
		
		try {      // for error handling
			match(LBRACE);
			match(SUBST);
			v=one_bound_variable();
			match(SEMI);
			if ( inputState.guessing==0 ) {
				// Tricky part, v cannot be bound while parsing a1
				if(!isGlobalDeclTermParser())
				unbindVars(orig);
				
			}
			a1=logicTermReEntry();
			if ( inputState.guessing==0 ) {
				// The rest of the tricky part, bind it again
				if(!isGlobalDeclTermParser())
				if(v instanceof LogicVariable)
				bindVar((LogicVariable)v);
					  else
					    bindVar();
				
			}
			match(RBRACE);
			{
			switch ( LA(1)) {
			case IF:
			case IFEX:
			case TRUE:
			case FALSE:
			case LPAREN:
			case LBRACE:
			case AT:
			case MINUS:
			case STRING_LITERAL:
			case CHAR_LITERAL:
			case IDENT:
			case NUM_LITERAL:
			{
				a2=term110();
				break;
			}
			case NOT:
			case FORALL:
			case EXISTS:
			case MODALITY:
			{
				a2=unary_formula();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
				result = TermBuilder.DF.subst ( op, v, a1, a2 );
				if(!isGlobalDeclTermParser())
				unbindVars(orig);
				
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final Term  updateterm() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		Term u = null; 
		Term a2 = null;
		
		
		try {      // for error handling
			match(LBRACE);
			u=term();
			match(RBRACE);
			{
			switch ( LA(1)) {
			case IF:
			case IFEX:
			case TRUE:
			case FALSE:
			case LPAREN:
			case LBRACE:
			case AT:
			case MINUS:
			case STRING_LITERAL:
			case CHAR_LITERAL:
			case IDENT:
			case NUM_LITERAL:
			{
				a2=term110();
				break;
			}
			case NOT:
			case FORALL:
			case EXISTS:
			case MODALITY:
			{
				a2=unary_formula();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				
					    result = tf.createTerm(UpdateApplication.UPDATE_APPLICATION, u, a2);
				
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
						(new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final QuantifiableVariable  one_bound_variable() throws RecognitionException, TokenStreamException {
		QuantifiableVariable v=null;
		
		
		try {      // for error handling
			if (((LA(1)==IDENT))&&(isGlobalDeclTermParser())) {
				v=one_logic_bound_variable_nosort();
			}
			else if (((LA(1)==IDENT))&&(inSchemaMode())) {
				v=one_schema_bound_variable();
			}
			else if (((LA(1)==IDENT))&&(!inSchemaMode())) {
				v=one_logic_bound_variable();
			}
			else {
				throw new NoViableAltException(LT(1), getFilename());
			}
			
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_6);
			} else {
			  throw ex;
			}
		}
		return v;
	}
	
	public final QuantifiableVariable  one_logic_bound_variable_nosort() throws RecognitionException, TokenStreamException {
		QuantifiableVariable v=null;
		
		
		String id = null;
		
		
		try {      // for error handling
			id=simple_ident();
			if ( inputState.guessing==0 ) {
				
				v = (LogicVariable)variables().lookup(new Name(id));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_6);
			} else {
			  throw ex;
			}
		}
		return v;
	}
	
	public final QuantifiableVariable  one_schema_bound_variable() throws RecognitionException, TokenStreamException {
		QuantifiableVariable v=null;
		
		
		String id = null;
		Operator ts = null;
		
		
		try {      // for error handling
			id=simple_ident();
			if ( inputState.guessing==0 ) {
				
				ts = (Operator) variables().lookup(new Name(id));   
				if ( ! (ts instanceof VariableSV)) {
				semanticError(ts+" is not allowed in a quantifier. Note, that you can't "
				+ "use the normal syntax for quantifiers of the form \"\\exists int i;\""
				+ " in taclets. You have to define the variable as a schema variable"
				+ " and use the syntax \"\\exists i;\" instead.");
				}
				v = (QuantifiableVariable) ts;
				bindVar();
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_6);
			} else {
			  throw ex;
			}
		}
		return v;
	}
	
	public final QuantifiableVariable  one_logic_bound_variable() throws RecognitionException, TokenStreamException {
		QuantifiableVariable v=null;
		
		
		Sort s = null;
		String id = null;
		
		
		try {      // for error handling
			s=sortId();
			id=simple_ident();
			if ( inputState.guessing==0 ) {
				
				v = bindVar(id, s);
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_41);
			} else {
			  throw ex;
			}
		}
		return v;
	}
	
	public final Term  metaTerm() throws RecognitionException, TokenStreamException {
		Term result = null;
		
		
		LinkedList al = new LinkedList();
		String param = null;
		TermTransformer vf = null;
		Term t = null;
		
		
		try {      // for error handling
			{
			vf=metaId();
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				match(LPAREN);
				t=term();
				if ( inputState.guessing==0 ) {
					
					al.add(t);
					
				}
				{
				_loop347:
				do {
					if ((LA(1)==COMMA)) {
						match(COMMA);
						t=term();
						if ( inputState.guessing==0 ) {
							
							al.add(t);
							
						}
					}
					else {
						break _loop347;
					}
					
				} while (true);
				}
				match(RPAREN);
				break;
			}
			case EOF:
			case MODIFIES:
			case DISPLAYNAME:
			case SLASH:
			case ASSIGN:
			case DOT:
			case DOTRANGE:
			case COMMA:
			case RPAREN:
			case RBRACE:
			case LBRACKET:
			case RBRACKET:
			case PARALLEL:
			case OR:
			case AND:
			case IMP:
			case EQUALS:
			case NOT_EQUALS:
			case SEQARROW:
			case PERCENT:
			case STAR:
			case MINUS:
			case PLUS:
			case GREATER:
			case GREATEREQUAL:
			case LESS:
			case LESSEQUAL:
			case LGUILLEMETS:
			case EQV:
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
					      
				result = tf.createTerm(vf, (Term[])al.toArray(AN_ARRAY_OF_TERMS));
				
			}
			}
		}
		catch (TermCreationException ex) {
			if (inputState.guessing==0) {
				
				keh.reportException
					    (new KeYSemanticException
							(ex.getMessage(), getFilename(), getLine(), getColumn()));
				
			} else {
				throw ex;
			}
		}
		return result;
	}
	
	public final String  arith_op() throws RecognitionException, TokenStreamException {
		String op = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case PERCENT:
			{
				match(PERCENT);
				if ( inputState.guessing==0 ) {
					op = "%";
				}
				break;
			}
			case STAR:
			{
				match(STAR);
				if ( inputState.guessing==0 ) {
					op = "*";
				}
				break;
			}
			case MINUS:
			{
				match(MINUS);
				if ( inputState.guessing==0 ) {
					op = "-";
				}
				break;
			}
			case SLASH:
			{
				match(SLASH);
				if ( inputState.guessing==0 ) {
					op = "/";
				}
				break;
			}
			case PLUS:
			{
				match(PLUS);
				if ( inputState.guessing==0 ) {
					op = "+";
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
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
		return op;
	}
	
	public final ParsableVariable  varId() throws RecognitionException, TokenStreamException {
		ParsableVariable v = null;
		
		Token  id = null;
		
		try {      // for error handling
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				
				v = (ParsableVariable) variables().lookup(new Name(id.getText()));
				if (v == null) {
				throw new NotDeclException("variable", id, 
				getFilename());
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		return v;
	}
	
	public final LinkedList  varIds() throws RecognitionException, TokenStreamException {
		LinkedList list = new LinkedList();
		
		
		ImmutableList<String> ids = null;
		ParsableVariable v = null;
		String id = null;
		
		
		try {      // for error handling
			ids=simple_ident_comma_list();
			if ( inputState.guessing==0 ) {
				
				Iterator<String> it = ids.iterator();
					 while(it.hasNext()) {
					    id = it.next();
				v = (ParsableVariable) variables().lookup(new Name(id));
				if (v == null) {
				semanticError("Variable " +id + " not declared.");
				}
					    list.add(v);
					 }
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_42);
			} else {
			  throw ex;
			}
		}
		return list;
	}
	
	public final Taclet  taclet(
		ImmutableSet<Choice> choices
	) throws RecognitionException, TokenStreamException {
		Taclet r;
		
		Token  name = null;
		
		Sequent ifSeq = Sequent.EMPTY_SEQUENT;
		Object  find = null;
		r = null;
		TacletBuilder b = null;
		int applicationRestriction = RewriteTaclet.NONE;
		
		
		try {      // for error handling
			name = LT(1);
			match(IDENT);
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				choices=option_list(choices);
				break;
			}
			case LBRACE:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(LBRACE);
			if ( inputState.guessing==0 ) {
				
					  //  schema var decls
					  namespaces().setVariables(new Namespace(variables()));
				
			}
			{
			_loop254:
			do {
				if ((LA(1)==SCHEMAVAR)) {
					match(SCHEMAVAR);
					one_schema_var_decl();
				}
				else {
					break _loop254;
				}
				
			} while (true);
			}
			{
			switch ( LA(1)) {
			case ASSUMES:
			{
				match(ASSUMES);
				match(LPAREN);
				ifSeq=seq();
				match(RPAREN);
				break;
			}
			case VARCOND:
			case CLOSEGOAL:
			case REPLACEWITH:
			case ADDRULES:
			case FIND:
			case ADD:
			case LPAREN:
			case STRING_LITERAL:
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
			case FIND:
			{
				match(FIND);
				match(LPAREN);
				find=termorseq();
				match(RPAREN);
				{
				_loop258:
				do {
					switch ( LA(1)) {
					case SAMEUPDATELEVEL:
					{
						match(SAMEUPDATELEVEL);
						if ( inputState.guessing==0 ) {
							applicationRestriction |= RewriteTaclet.SAME_UPDATE_LEVEL;
						}
						break;
					}
					case INSEQUENTSTATE:
					{
						match(INSEQUENTSTATE);
						if ( inputState.guessing==0 ) {
							applicationRestriction |= RewriteTaclet.IN_SEQUENT_STATE;
						}
						break;
					}
					case ANTECEDENTPOLARITY:
					{
						match(ANTECEDENTPOLARITY);
						if ( inputState.guessing==0 ) {
							applicationRestriction |= RewriteTaclet.ANTECEDENT_POLARITY;
						}
						break;
					}
					case SUCCEDENTPOLARITY:
					{
						match(SUCCEDENTPOLARITY);
						if ( inputState.guessing==0 ) {
							applicationRestriction |= RewriteTaclet.SUCCEDENT_POLARITY;
						}
						break;
					}
					default:
					{
						break _loop258;
					}
					}
				} while (true);
				}
				break;
			}
			case VARCOND:
			case CLOSEGOAL:
			case REPLACEWITH:
			case ADDRULES:
			case ADD:
			case LPAREN:
			case STRING_LITERAL:
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
				
				b = createTacletBuilderFor(find, applicationRestriction);
				b.setName(new Name(name.getText()));
				b.setIfSequent(ifSeq);
				
			}
			{
			switch ( LA(1)) {
			case VARCOND:
			{
				match(VARCOND);
				match(LPAREN);
				varexplist(b);
				match(RPAREN);
				break;
			}
			case CLOSEGOAL:
			case REPLACEWITH:
			case ADDRULES:
			case ADD:
			case LPAREN:
			case STRING_LITERAL:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			goalspecs(b, find != null);
			modifiers(b);
			match(RBRACE);
			if ( inputState.guessing==0 ) {
				
				b.setChoices(choices);
				r = b.getTaclet(); 
				taclet2Builder.put(r,b);
					  // dump local schema var decls
					  namespaces().setVariables(variables().parent());
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_41);
			} else {
			  throw ex;
			}
		}
		return r;
	}
	
	public final ImmutableSet<Choice>  option_list(
		ImmutableSet<Choice> soc
	) throws RecognitionException, TokenStreamException {
		ImmutableSet<Choice> result = null;
		
		
		Choice c = null;
		
		
		try {      // for error handling
			match(LPAREN);
			if ( inputState.guessing==0 ) {
				result = soc;
			}
			c=option();
			if ( inputState.guessing==0 ) {
				result = result.add(c);
			}
			{
			_loop319:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					c=option();
					if ( inputState.guessing==0 ) {
						result = result.add(c);
					}
				}
				else {
					break _loop319;
				}
				
			} while (true);
			}
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_43);
			} else {
			  throw ex;
			}
		}
		return result;
	}
	
	public final Sequent  seq() throws RecognitionException, TokenStreamException {
		Sequent s;
		
		Semisequent ant,suc; s = null;
		
		try {      // for error handling
			ant=semisequent();
			match(SEQARROW);
			suc=semisequent();
			if ( inputState.guessing==0 ) {
				s = Sequent.createSequent(ant, suc);
			}
		}
		catch (RuntimeException ex) {
			if (inputState.guessing==0) {
				
				KeYSemanticException betterEx = 
				
					 new KeYSemanticException(ex.getMessage(), getFilename(), getLine(), getColumn());
					 betterEx.setStackTrace(ex.getStackTrace());	
					 keh.reportException(betterEx);			
				
			} else {
				throw ex;
			}
		}
		return s;
	}
	
	public final Object  termorseq() throws RecognitionException, TokenStreamException {
		Object o;
		
		
		Term head = null;
		Sequent s = null;
		Semisequent ss = null;
		o = null; 
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case NOT:
			case FORALL:
			case EXISTS:
			case IF:
			case IFEX:
			case TRUE:
			case FALSE:
			case LPAREN:
			case LBRACE:
			case AT:
			case MINUS:
			case STRING_LITERAL:
			case CHAR_LITERAL:
			case IDENT:
			case NUM_LITERAL:
			case MODALITY:
			{
				head=term();
				{
				switch ( LA(1)) {
				case COMMA:
				{
					match(COMMA);
					s=seq();
					break;
				}
				case SEQARROW:
				{
					match(SEQARROW);
					ss=semisequent();
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
				if ( inputState.guessing==0 ) {
					
					if ( s == null ) {
					if ( ss == null ) {
					// Just a term
					o = head;
					} else {
					// A sequent with only head in the antecedent.
					Semisequent ant = Semisequent.EMPTY_SEMISEQUENT;
					ant = ant.insertFirst(
					new SequentFormula(head)).semisequent();
					o = Sequent.createSequent(ant,ss);
					}
					} else {
					// A sequent.  Prepend head to the antecedent.
					Semisequent newAnt = s.antecedent();
					newAnt = newAnt .insertFirst(
					new SequentFormula(head)).semisequent();
					o = Sequent.createSequent(newAnt,s.succedent());
					}
					
				}
				break;
			}
			case SEQARROW:
			{
				match(SEQARROW);
				ss=semisequent();
				if ( inputState.guessing==0 ) {
					
					o = Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,ss);
					
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_42);
			} else {
			  throw ex;
			}
		}
		return o;
	}
	
	public final void varexplist(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			varexp(b);
			{
			_loop270:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					varexp(b);
				}
				else {
					break _loop270;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_42);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void goalspecs(
		TacletBuilder b, boolean ruleWithFind
	) throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case CLOSEGOAL:
			{
				match(CLOSEGOAL);
				break;
			}
			case REPLACEWITH:
			case ADDRULES:
			case ADD:
			case LPAREN:
			case STRING_LITERAL:
			{
				goalspecwithoption(b, ruleWithFind);
				{
				_loop312:
				do {
					if ((LA(1)==SEMI)) {
						match(SEMI);
						goalspecwithoption(b, ruleWithFind);
					}
					else {
						break _loop312;
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
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_44);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void modifiers(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		Vector rs = null;
		String dname= null;
		String oname= null;
		String htext = null;
		
		
		try {      // for error handling
			{
			_loop262:
			do {
				switch ( LA(1)) {
				case HEURISTICS:
				{
					rs=rulesets();
					if ( inputState.guessing==0 ) {
						
						Iterator it = rs.iterator();
						while(it.hasNext())
						b.addRuleSet((RuleSet)it.next());
						
					}
					break;
				}
				case NONINTERACTIVE:
				{
					match(NONINTERACTIVE);
					if ( inputState.guessing==0 ) {
						b.addRuleSet((RuleSet)ruleSets().lookup(new Name("notHumanReadable")));
					}
					break;
				}
				case DISPLAYNAME:
				{
					match(DISPLAYNAME);
					dname=string_literal();
					if ( inputState.guessing==0 ) {
						b.setDisplayName(dname);
					}
					break;
				}
				case HELPTEXT:
				{
					match(HELPTEXT);
					htext=string_literal();
					if ( inputState.guessing==0 ) {
						b.setHelpText(htext);
					}
					break;
				}
				default:
				{
					break _loop262;
				}
				}
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_45);
			} else {
			  throw ex;
			}
		}
	}
	
	public final Vector  rulesets() throws RecognitionException, TokenStreamException {
		Vector rs = new Vector();
		
		
		try {      // for error handling
			match(HEURISTICS);
			match(LPAREN);
			ruleset(rs);
			{
			_loop340:
			do {
				if ((LA(1)==COMMA)) {
					match(COMMA);
					ruleset(rs);
				}
				else {
					break _loop340;
				}
				
			} while (true);
			}
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_44);
			} else {
			  throw ex;
			}
		}
		return rs;
	}
	
	public final Semisequent  semisequent() throws RecognitionException, TokenStreamException {
		Semisequent ss;
		
		
		Term head = null;
		ss = Semisequent.EMPTY_SEMISEQUENT; 
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case RPAREN:
			case SEQARROW:
			{
				break;
			}
			case NOT:
			case FORALL:
			case EXISTS:
			case IF:
			case IFEX:
			case TRUE:
			case FALSE:
			case LPAREN:
			case LBRACE:
			case AT:
			case MINUS:
			case STRING_LITERAL:
			case CHAR_LITERAL:
			case IDENT:
			case NUM_LITERAL:
			case MODALITY:
			{
				head=term();
				{
				switch ( LA(1)) {
				case COMMA:
				{
					match(COMMA);
					ss=semisequent();
					break;
				}
				case RPAREN:
				case SEQARROW:
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
					
					ss = ss.insertFirst(new SequentFormula(head)).semisequent(); 
					
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_46);
			} else {
			  throw ex;
			}
		}
		return ss;
	}
	
	public final void varexp(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		boolean negated = false;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case APPLY_UPDATE_ON_RIGID:
			case DROP_EFFECTLESS_ELEMENTARIES:
			case DROP_EFFECTLESS_STORES:
			case SIMPLIFY_IF_THEN_ELSE_UPDATE:
			case ENUM_CONST:
			case HASSORT:
			case FIELDTYPE:
			case ISOBSERVER:
			case DIFFERENT:
			case METADISJOINT:
			case EQUAL_UNIQUE:
			case NEW:
			case NEWLABEL:
			case NOTFREEIN:
			{
				{
				switch ( LA(1)) {
				case APPLY_UPDATE_ON_RIGID:
				{
					varcond_applyUpdateOnRigid(b);
					break;
				}
				case DROP_EFFECTLESS_ELEMENTARIES:
				{
					varcond_dropEffectlessElementaries(b);
					break;
				}
				case DROP_EFFECTLESS_STORES:
				{
					varcond_dropEffectlessStores(b);
					break;
				}
				case ENUM_CONST:
				{
					varcond_enum_const(b);
					break;
				}
				case NOTFREEIN:
				{
					varcond_free(b);
					break;
				}
				case HASSORT:
				{
					varcond_hassort(b);
					break;
				}
				case FIELDTYPE:
				{
					varcond_fieldtype(b);
					break;
				}
				case EQUAL_UNIQUE:
				{
					varcond_equalUnique(b);
					break;
				}
				case NEW:
				{
					varcond_new(b);
					break;
				}
				case NEWLABEL:
				{
					varcond_newlabel(b);
					break;
				}
				case ISOBSERVER:
				{
					varcond_observer(b);
					break;
				}
				case DIFFERENT:
				{
					varcond_different(b);
					break;
				}
				case METADISJOINT:
				{
					varcond_metadisjoint(b);
					break;
				}
				case SIMPLIFY_IF_THEN_ELSE_UPDATE:
				{
					varcond_simplifyIfThenElseUpdate(b);
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
			case DISJOINTMODULONULL:
			case FREELABELIN:
			case ISARRAY:
			case ISARRAYLENGTH:
			case ISENUMTYPE:
			case ISINDUCTVAR:
			case ISLOCALVARIABLE:
			case ISREFERENCE:
			case ISREFERENCEARRAY:
			case ISSUBTYPE:
			case NOT:
			case SAME:
			case STATIC:
			case STATICMETHODREFERENCE:
			case STRICT:
			case IS_ABSTRACT_OR_INTERFACE:
			{
				{
				{
				switch ( LA(1)) {
				case NOT:
				{
					match(NOT);
					if ( inputState.guessing==0 ) {
						negated = true;
					}
					break;
				}
				case DISJOINTMODULONULL:
				case FREELABELIN:
				case ISARRAY:
				case ISARRAYLENGTH:
				case ISENUMTYPE:
				case ISINDUCTVAR:
				case ISLOCALVARIABLE:
				case ISREFERENCE:
				case ISREFERENCEARRAY:
				case ISSUBTYPE:
				case SAME:
				case STATIC:
				case STATICMETHODREFERENCE:
				case STRICT:
				case IS_ABSTRACT_OR_INTERFACE:
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
				case IS_ABSTRACT_OR_INTERFACE:
				{
					varcond_abstractOrInterface(b, negated);
					break;
				}
				case ISARRAY:
				{
					varcond_array(b, negated);
					break;
				}
				case ISARRAYLENGTH:
				{
					varcond_array_length(b, negated);
					break;
				}
				case ISENUMTYPE:
				{
					varcond_enumtype(b, negated);
					break;
				}
				case FREELABELIN:
				{
					varcond_freeLabelIn(b,negated);
					break;
				}
				case ISLOCALVARIABLE:
				{
					varcond_localvariable(b, negated);
					break;
				}
				case ISREFERENCE:
				{
					varcond_reference(b, negated);
					break;
				}
				case ISREFERENCEARRAY:
				{
					varcond_referencearray(b, negated);
					break;
				}
				case STATIC:
				{
					varcond_static(b,negated);
					break;
				}
				case STATICMETHODREFERENCE:
				{
					varcond_staticmethod(b,negated);
					break;
				}
				case DISJOINTMODULONULL:
				case ISSUBTYPE:
				case SAME:
				case STRICT:
				{
					varcond_typecheck(b, negated);
					break;
				}
				case ISINDUCTVAR:
				{
					varcond_induction_variable(b, negated);
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
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_applyUpdateOnRigid(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable u = null;
		ParsableVariable x = null;
		ParsableVariable x2 = null;
		
		
		try {      // for error handling
			match(APPLY_UPDATE_ON_RIGID);
			match(LPAREN);
			u=varId();
			match(COMMA);
			x=varId();
			match(COMMA);
			x2=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new ApplyUpdateOnRigidCondition((UpdateSV)u, 
				(SchemaVariable)x, 
				(SchemaVariable)x2));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_dropEffectlessElementaries(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable u = null;
		ParsableVariable x = null;
		ParsableVariable result = null;
		
		
		try {      // for error handling
			match(DROP_EFFECTLESS_ELEMENTARIES);
			match(LPAREN);
			u=varId();
			match(COMMA);
			x=varId();
			match(COMMA);
			result=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new DropEffectlessElementariesCondition((UpdateSV)u, 
				(SchemaVariable)x, 
				(SchemaVariable)result));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_dropEffectlessStores(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable h = null;
		ParsableVariable o = null;
		ParsableVariable f = null;
		ParsableVariable x = null;
		ParsableVariable result = null;
		
		
		try {      // for error handling
			match(DROP_EFFECTLESS_STORES);
			match(LPAREN);
			h=varId();
			match(COMMA);
			o=varId();
			match(COMMA);
			f=varId();
			match(COMMA);
			x=varId();
			match(COMMA);
			result=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new DropEffectlessStoresCondition((TermSV)h,
											       (TermSV)o,
											       (TermSV)f,
											       (TermSV)x, 
				(TermSV)result));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_enum_const(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		
		
		try {      // for error handling
			match(ENUM_CONST);
			match(LPAREN);
			x=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new EnumConstantCondition(
					(SchemaVariable) x));     
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_free(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		LinkedList ys = null;
		
		
		try {      // for error handling
			match(NOTFREEIN);
			match(LPAREN);
			x=varId();
			match(COMMA);
			ys=varIds();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				Iterator it = ys.iterator();
				while(it.hasNext()) {
				b.addVarsNotFreeIn((SchemaVariable)x,(SchemaVariable)it.next());
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_hassort(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		Sort s = null;
		boolean elemSort = false;
		
		
		try {      // for error handling
			match(HASSORT);
			match(LPAREN);
			{
			switch ( LA(1)) {
			case IDENT:
			{
				x=varId();
				break;
			}
			case ELEMSORT:
			{
				match(ELEMSORT);
				match(LPAREN);
				x=varId();
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					elemSort = true;
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(COMMA);
			s=any_sortId_check(true);
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				if(!(s instanceof GenericSort)) {
					 throw new GenericSortException("sort",
									"Generic sort expected", 
									s,
									getFilename(),
									getLine(), 
									getColumn());
				} else if (!JavaTypeToSortCondition.checkSortedSV((SchemaVariable)x)) {
					 semanticError("Expected schema variable of kind EXPRESSION or TYPE, " 
					 	       + "but is " + x);
				} else {
				b.addVariableCondition(new JavaTypeToSortCondition((SchemaVariable)x, 
											    (GenericSort)s,
											    elemSort));
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_fieldtype(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		Sort s = null;
		
		
		try {      // for error handling
			match(FIELDTYPE);
			match(LPAREN);
			x=varId();
			match(COMMA);
			s=any_sortId_check(true);
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				if(!(s instanceof GenericSort)) {
				throw new GenericSortException("sort",
				"Generic sort expected", 
				s,
				getFilename(),
				getLine(), 
				getColumn());
				} else if(!FieldTypeToSortCondition.checkSortedSV((SchemaVariable)x)) {
				semanticError("Expected schema variable of kind EXPRESSION or TYPE, " 
				+ "but is " + x);
				} else {
				b.addVariableCondition(new FieldTypeToSortCondition((SchemaVariable)x, 
				(GenericSort)s));
				}
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_equalUnique(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable t = null;
		ParsableVariable t2 = null;
		ParsableVariable phi = null;
		
		
		try {      // for error handling
			match(EQUAL_UNIQUE);
			match(LPAREN);
			t=varId();
			match(COMMA);
			t2=varId();
			match(COMMA);
			phi=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					   b.addVariableCondition(new EqualUniqueCondition((TermSV) t, 
					                                                   (TermSV) t2, 
					                                                   (FormulaSV) phi));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_new(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null, y = null;
		KeYJavaType kjt = null;
		
		
		try {      // for error handling
			match(NEW);
			match(LPAREN);
			x=varId();
			match(COMMA);
			{
			switch ( LA(1)) {
			case TYPEOF:
			{
				match(TYPEOF);
				match(LPAREN);
				y=varId();
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					
						    b.addVarsNew((SchemaVariable) x, (SchemaVariable) y);
						
				}
				break;
			}
			case DEPENDINGON:
			{
				match(DEPENDINGON);
				match(LPAREN);
				y=varId();
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					
						    b.addVarsNewDependingOn((SchemaVariable)x, (SchemaVariable)y);
						
				}
				break;
			}
			case IDENT:
			{
				kjt=keyjavatype();
				if ( inputState.guessing==0 ) {
					
							b.addVarsNew((SchemaVariable) x, kjt.getJavaType());
						
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_newlabel(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x;
		
		
		try {      // for error handling
			match(NEWLABEL);
			match(LPAREN);
			x=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new NewJumpLabelCondition((SchemaVariable)x));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_observer(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable obs = null;
		ParsableVariable heap = null;
		ParsableVariable obj = null;
		
		
		try {      // for error handling
			match(ISOBSERVER);
			match(LPAREN);
			obs=varId();
			match(COMMA);
			heap=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					   b.addVariableCondition(new ObserverCondition((TermSV)obs, 
					                                                (TermSV)heap));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_different(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable var1, var2;
		
		
		try {      // for error handling
			match(DIFFERENT);
			match(LPAREN);
			var1=varId();
			match(COMMA);
			var2=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					   b.addVariableCondition(new DifferentInstantiationCondition(
					   				(SchemaVariable)var1,
					   				 (SchemaVariable)var2));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_metadisjoint(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable var1, var2;
		
		
		try {      // for error handling
			match(METADISJOINT);
			match(LPAREN);
			var1=varId();
			match(COMMA);
			var2=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					   b.addVariableCondition(new MetaDisjointCondition(
					   				(TermSV)var1,
					   				(TermSV)var2));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_simplifyIfThenElseUpdate(
		TacletBuilder b
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable u1 = null;
		ParsableVariable u2 = null;
		ParsableVariable commonFormula  = null;
		ParsableVariable phi = null;
		ParsableVariable result = null;
		
		
		try {      // for error handling
			match(SIMPLIFY_IF_THEN_ELSE_UPDATE);
			match(LPAREN);
			phi=varId();
			match(COMMA);
			u1=varId();
			match(COMMA);
			u2=varId();
			match(COMMA);
			commonFormula=varId();
			match(COMMA);
			result=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new SimplifyIfThenElseUpdateCondition((FormulaSV) phi,
																			   (UpdateSV) u1,
																			   (UpdateSV) u2,
																			   (FormulaSV) commonFormula,
				(SchemaVariable)result));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_abstractOrInterface(
		TacletBuilder b, boolean negated
	) throws RecognitionException, TokenStreamException {
		
		
		TypeResolver tr = null;
		
		
		try {      // for error handling
			match(IS_ABSTRACT_OR_INTERFACE);
			match(LPAREN);
			tr=type_resolver();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new AbstractOrInterfaceType(tr, negated));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_array(
		TacletBuilder b, boolean negated
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		
		
		try {      // for error handling
			match(ISARRAY);
			match(LPAREN);
			x=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new ArrayTypeCondition(
				(SchemaVariable)x, negated));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_array_length(
		TacletBuilder b, boolean negated
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		
		
		try {      // for error handling
			match(ISARRAYLENGTH);
			match(LPAREN);
			x=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new ArrayLengthCondition (
				(SchemaVariable)x, negated));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_enumtype(
		TacletBuilder b, boolean negated
	) throws RecognitionException, TokenStreamException {
		
		
		TypeResolver tr = null;
		
		
		try {      // for error handling
			match(ISENUMTYPE);
			match(LPAREN);
			tr=type_resolver();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new EnumTypeCondition(tr, negated));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_freeLabelIn(
		TacletBuilder b, boolean negated
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable label = null, statement = null;
		
		
		try {      // for error handling
			match(FREELABELIN);
			match(LPAREN);
			label=varId();
			match(COMMA);
			statement=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					b.addVariableCondition(new FreeLabelInVariableCondition((SchemaVariable) label, 
					(SchemaVariable) statement, negated ));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_localvariable(
		TacletBuilder b, boolean negated
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		
		
		try {      // for error handling
			match(ISLOCALVARIABLE);
			match(LPAREN);
			x=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					   b.addVariableCondition(new LocalVariableCondition((SchemaVariable) x, negated));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_reference(
		TacletBuilder b, boolean isPrimitive
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		TypeResolver tr = null;
		String id = null;
		boolean nonNull = false;
		
		
		try {      // for error handling
			match(ISREFERENCE);
			{
			switch ( LA(1)) {
			case LBRACKET:
			{
				match(LBRACKET);
				id=simple_ident();
				if ( inputState.guessing==0 ) {
						
						if ("non_null".equals(id)) {
						    nonNull = true;
						} else {	   
					semanticError(id + 
						      " is not an allowed modifier for the \\isReference variable condition.");
						}                   	
					
				}
				match(RBRACKET);
				break;
			}
			case LPAREN:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			match(LPAREN);
			tr=type_resolver();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				b.addVariableCondition(new TypeCondition(tr, !isPrimitive, nonNull));
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_referencearray(
		TacletBuilder b, boolean primitiveElementType
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		
		
		try {      // for error handling
			match(ISREFERENCEARRAY);
			match(LPAREN);
			x=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new ArrayComponentTypeCondition(
				(SchemaVariable)x, !primitiveElementType));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_static(
		TacletBuilder b, boolean negated
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		
		
		try {      // for error handling
			match(STATIC);
			match(LPAREN);
			x=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new StaticReferenceCondition(
					(SchemaVariable) x, negated));     
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_staticmethod(
		TacletBuilder b, boolean negated
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null, y = null, z = null;
		
		
		try {      // for error handling
			match(STATICMETHODREFERENCE);
			match(LPAREN);
			x=varId();
			match(COMMA);
			y=varId();
			match(COMMA);
			z=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new StaticMethodCondition
				(negated, (SchemaVariable)x, (SchemaVariable)y, (SchemaVariable)z));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_typecheck(
		TacletBuilder b, boolean negated
	) throws RecognitionException, TokenStreamException {
		
		
		TypeResolver fst = null, snd = null;
		TypeComparisonCondition.Mode mode = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case SAME:
			{
				match(SAME);
				if ( inputState.guessing==0 ) {
						
						  mode = negated 
						         ? TypeComparisonCondition.Mode.NOT_SAME 
						         : TypeComparisonCondition.Mode.SAME;
					
				}
				break;
			}
			case ISSUBTYPE:
			{
				match(ISSUBTYPE);
				if ( inputState.guessing==0 ) {
					
					mode = negated 
					? TypeComparisonCondition.Mode.NOT_IS_SUBTYPE
					: TypeComparisonCondition.Mode.IS_SUBTYPE; 
					
				}
				break;
			}
			case STRICT:
			{
				match(STRICT);
				match(ISSUBTYPE);
				if ( inputState.guessing==0 ) {
					
					if(negated) {  
						      semanticError("A negated strict subtype check does not make sense.");
						  } 
						  mode = TypeComparisonCondition.Mode.STRICT_SUBTYPE;
					
				}
				break;
			}
			case DISJOINTMODULONULL:
			{
				match(DISJOINTMODULONULL);
				if ( inputState.guessing==0 ) {
					
					if(negated) {
					semanticError("Negation not supported");
					}
					mode = TypeComparisonCondition.Mode.DISJOINTMODULONULL;
					
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
			fst=type_resolver();
			match(COMMA);
			snd=type_resolver();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
					b.addVariableCondition(new TypeComparisonCondition(fst, snd, mode));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void varcond_induction_variable(
		TacletBuilder b, boolean negated
	) throws RecognitionException, TokenStreamException {
		
		
		ParsableVariable x = null;
		
		
		try {      // for error handling
			match(ISINDUCTVAR);
			match(LPAREN);
			x=varId();
			match(RPAREN);
			if ( inputState.guessing==0 ) {
				
				b.addVariableCondition(new InductionVariableCondition (
				(SchemaVariable)x, negated ));
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final TypeResolver  type_resolver() throws RecognitionException, TokenStreamException {
		TypeResolver tr = null;
		
		
		Sort s = null;
		ParsableVariable y = null;
		ParsableVariable z = null;
		
		
		try {      // for error handling
			switch ( LA(1)) {
			case IDENT:
			{
				{
				s=any_sortId_check(true);
				if ( inputState.guessing==0 ) {
					
					if ( s instanceof GenericSort ) {
					tr = TypeResolver.createGenericSortResolver((GenericSort)s);
					} else {
					tr = TypeResolver.createNonGenericSortResolver(s);
					}
					
				}
				}
				break;
			}
			case TYPEOF:
			{
				{
				match(TYPEOF);
				match(LPAREN);
				y=varId();
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					
					tr = TypeResolver.createElementTypeResolver((SchemaVariable)y); 
					
				}
				}
				break;
			}
			case CONTAINERTYPE:
			{
				{
				match(CONTAINERTYPE);
				match(LPAREN);
				y=varId();
				match(RPAREN);
				if ( inputState.guessing==0 ) {
					
					tr = TypeResolver.createContainerTypeResolver((SchemaVariable)y); 
					
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
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		return tr;
	}
	
	public final void goalspecwithoption(
		TacletBuilder b, boolean ruleWithFind
	) throws RecognitionException, TokenStreamException {
		
		
		ImmutableSet<Choice> soc = DefaultImmutableSet.<Choice>nil();
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case LPAREN:
			{
				{
				soc=option_list(soc);
				match(LBRACE);
				goalspec(b,soc,ruleWithFind);
				match(RBRACE);
				}
				break;
			}
			case REPLACEWITH:
			case ADDRULES:
			case ADD:
			case STRING_LITERAL:
			{
				goalspec(b,null,ruleWithFind);
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_47);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void goalspec(
		TacletBuilder b, ImmutableSet<Choice> soc, boolean ruleWithFind
	) throws RecognitionException, TokenStreamException {
		
		
		Object rwObj = null;
		Sequent addSeq = Sequent.EMPTY_SEQUENT;
		ImmutableList<Taclet> addRList = ImmutableSLList.<Taclet>nil();
		ImmutableSet<SchemaVariable> addpv = DefaultImmutableSet.<SchemaVariable>nil();
		String name = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case STRING_LITERAL:
			{
				name=string_literal();
				match(COLON);
				break;
			}
			case REPLACEWITH:
			case ADDRULES:
			case ADD:
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
			case REPLACEWITH:
			{
				{
				rwObj=replacewith();
				{
				switch ( LA(1)) {
				case ADD:
				{
					addSeq=add();
					break;
				}
				case NONINTERACTIVE:
				case DISPLAYNAME:
				case HELPTEXT:
				case ADDRULES:
				case ADDPROGVARS:
				case HEURISTICS:
				case SEMI:
				case RBRACE:
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
				case ADDRULES:
				{
					addRList=addrules();
					break;
				}
				case NONINTERACTIVE:
				case DISPLAYNAME:
				case HELPTEXT:
				case ADDPROGVARS:
				case HEURISTICS:
				case SEMI:
				case RBRACE:
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
				case ADDPROGVARS:
				{
					addpv=addprogvar();
					break;
				}
				case NONINTERACTIVE:
				case DISPLAYNAME:
				case HELPTEXT:
				case HEURISTICS:
				case SEMI:
				case RBRACE:
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
			case ADD:
			{
				{
				addSeq=add();
				{
				switch ( LA(1)) {
				case ADDRULES:
				{
					addRList=addrules();
					break;
				}
				case NONINTERACTIVE:
				case DISPLAYNAME:
				case HELPTEXT:
				case HEURISTICS:
				case SEMI:
				case RBRACE:
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
			case ADDRULES:
			{
				{
				addRList=addrules();
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
				
				addGoalTemplate(b,name,rwObj,addSeq,addRList,addpv,soc);
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_47);
			} else {
			  throw ex;
			}
		}
	}
	
	public final Choice  option() throws RecognitionException, TokenStreamException {
		Choice c=null;
		
		Token  cat = null;
		Token  choice = null;
		
		try {      // for error handling
			cat = LT(1);
			match(IDENT);
			match(COLON);
			choice = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				
				c = (Choice) choices().lookup(new Name(cat.getText()+":"+choice.getText()));
				if(c==null) {
				throw new NotDeclException
							("Option", choice, getFilename());
					    }
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
		return c;
	}
	
	public final Object  replacewith() throws RecognitionException, TokenStreamException {
		Object o;
		
		o = null;
		
		try {      // for error handling
			match(REPLACEWITH);
			match(LPAREN);
			o=termorseq();
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_48);
			} else {
			  throw ex;
			}
		}
		return o;
	}
	
	public final Sequent  add() throws RecognitionException, TokenStreamException {
		Sequent s;
		
		s = null;
		
		try {      // for error handling
			match(ADD);
			match(LPAREN);
			s=seq();
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_49);
			} else {
			  throw ex;
			}
		}
		return s;
	}
	
	public final ImmutableList<Taclet>  addrules() throws RecognitionException, TokenStreamException {
		ImmutableList<Taclet> lor;
		
		lor = null;
		
		try {      // for error handling
			match(ADDRULES);
			match(LPAREN);
			lor=tacletlist();
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_50);
			} else {
			  throw ex;
			}
		}
		return lor;
	}
	
	public final ImmutableSet<SchemaVariable>  addprogvar() throws RecognitionException, TokenStreamException {
		ImmutableSet<SchemaVariable> pvs;
		
		pvs = null;
		
		try {      // for error handling
			match(ADDPROGVARS);
			match(LPAREN);
			pvs=pvset();
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_47);
			} else {
			  throw ex;
			}
		}
		return pvs;
	}
	
	public final ImmutableList<Taclet>  tacletlist() throws RecognitionException, TokenStreamException {
		ImmutableList<Taclet> lor;
		
		
		Taclet head = null;
		lor = ImmutableSLList.<Taclet>nil(); 
		
		
		try {      // for error handling
			head=taclet(DefaultImmutableSet.<Choice>nil());
			{
			switch ( LA(1)) {
			case RPAREN:
			{
				break;
			}
			case COMMA:
			{
				match(COMMA);
				lor=tacletlist();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				lor = lor.prepend(head);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_42);
			} else {
			  throw ex;
			}
		}
		return lor;
	}
	
	public final ImmutableSet<SchemaVariable>  pvset() throws RecognitionException, TokenStreamException {
		ImmutableSet<SchemaVariable> pvs;
		
		
		ParsableVariable pv = null;
		pvs = DefaultImmutableSet.<SchemaVariable>nil();
		
		
		try {      // for error handling
			pv=varId();
			{
			switch ( LA(1)) {
			case RPAREN:
			{
				break;
			}
			case COMMA:
			{
				match(COMMA);
				pvs=pvset();
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			if ( inputState.guessing==0 ) {
				pvs = pvs.add
				((SchemaVariable)pv);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_42);
			} else {
			  throw ex;
			}
		}
		return pvs;
	}
	
	public final void ruleset(
		Vector rs
	) throws RecognitionException, TokenStreamException {
		
		Token  id = null;
		
		try {      // for error handling
			id = LT(1);
			match(IDENT);
			if ( inputState.guessing==0 ) {
				
				RuleSet h = (RuleSet) ruleSets().lookup(new Name(id.getText()));
				if (h == null) {
				throw new NotDeclException("ruleset", id, getFilename());
				}
				rs.add(h);
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_40);
			} else {
			  throw ex;
			}
		}
	}
	
	public final TermTransformer  metaId() throws RecognitionException, TokenStreamException {
		TermTransformer v = null;
		
		
		String id = null;
		
		
		try {      // for error handling
			id=simple_ident();
			if ( inputState.guessing==0 ) {
				
				v = AbstractTermTransformer.name2metaop(id);
				if (v == null)
				semanticError("Unknown metaoperator: "+id);
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_51);
			} else {
			  throw ex;
			}
		}
		return v;
	}
	
	public final void contracts() throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(CONTRACTS);
			match(LBRACE);
			if ( inputState.guessing==0 ) {
				
					    switchToNormalMode();
				
			}
			{
			_loop350:
			do {
				if ((LA(1)==IDENT)) {
					one_contract();
				}
				else {
					break _loop350;
				}
				
			} while (true);
			}
			match(RBRACE);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_2);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void one_contract() throws RecognitionException, TokenStreamException {
		
		
		Term fma = null;
		Term modifiesClause = null;
		String displayName = null;
		String contractName = null;
		Vector rs = null;
		NamespaceSet oldServicesNamespaces = null;
		
		
		try {      // for error handling
			contractName=simple_ident();
			match(LBRACE);
			if ( inputState.guessing==0 ) {
				
				//for program variable declarations
				namespaces().setProgramVariables(new Namespace(programVariables()));    
				
			}
			{
			switch ( LA(1)) {
			case PROGRAMVARIABLES:
			{
				prog_var_decls();
				break;
			}
			case NOT:
			case FORALL:
			case EXISTS:
			case IF:
			case IFEX:
			case TRUE:
			case FALSE:
			case LPAREN:
			case LBRACE:
			case AT:
			case MINUS:
			case STRING_LITERAL:
			case CHAR_LITERAL:
			case IDENT:
			case NUM_LITERAL:
			case MODALITY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(LT(1), getFilename());
			}
			}
			}
			fma=formula();
			match(MODIFIES);
			modifiesClause=term();
			if ( inputState.guessing==0 ) {
				
				DLSpecFactory dsf = new DLSpecFactory(getServices());
				try {
				contracts = contracts.add(dsf.createDLOperationContract(contractName,
									                         fma, 
								                         modifiesClause));
				} catch(ProofInputException e) {
				semanticError(e.getMessage());
				}
				
			}
			match(RBRACE);
			match(SEMI);
			if ( inputState.guessing==0 ) {
				
				//dump local program variable declarations
				namespaces().setProgramVariables(programVariables().parent());
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_20);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void invariants() throws RecognitionException, TokenStreamException {
		
		
		QuantifiableVariable selfVar;
		Namespace orig = variables();  
		
		
		try {      // for error handling
			match(INVARIANTS);
			match(LPAREN);
			selfVar=one_logic_bound_variable();
			match(RPAREN);
			match(LBRACE);
			if ( inputState.guessing==0 ) {
				
					    switchToNormalMode();
				
			}
			{
			_loop353:
			do {
				if ((LA(1)==IDENT)) {
					one_invariant((ParsableVariable)selfVar);
				}
				else {
					break _loop353;
				}
				
			} while (true);
			}
			match(RBRACE);
			if ( inputState.guessing==0 ) {
				
				unbindVars(orig);
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_52);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void one_invariant(
		ParsableVariable selfVar
	) throws RecognitionException, TokenStreamException {
		
		
		Term fma = null;
		String displayName = null;
		String invName = null;
		
		
		try {      // for error handling
			invName=simple_ident();
			match(LBRACE);
			fma=formula();
			{
			switch ( LA(1)) {
			case DISPLAYNAME:
			{
				match(DISPLAYNAME);
				displayName=string_literal();
				break;
			}
			case RBRACE:
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
				
				DLSpecFactory dsf = new DLSpecFactory(getServices());
				try {
				invs = invs.add(dsf.createDLClassInvariant(invName,
				displayName,
				selfVar,
				fma));
				} catch(ProofInputException e) {
				semanticError(e.getMessage());
				}
				
			}
			match(RBRACE);
			match(SEMI);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_20);
			} else {
			  throw ex;
			}
		}
	}
	
	public final Term  problem() throws RecognitionException, TokenStreamException {
		 Term a = null ;
		
		
		Taclet s = null;
		ImmutableSet<Choice> choices=DefaultImmutableSet.<Choice>nil();
		Choice c = null;
		ImmutableList<String> stlist = null;
		String string = null;
		String pref = null;
		
		
		try {      // for error handling
			if ( inputState.guessing==0 ) {
				if (capturer != null) capturer.mark();
			}
			{
			pref=preferences();
			}
			if ( inputState.guessing==0 ) {
				if ((pref!=null) && (capturer != null)) capturer.mark();
			}
			string=bootClassPath();
			stlist=classPaths();
			string=javaSource();
			decls();
			if ( inputState.guessing==0 ) {
				
				if(parse_includes || onlyWith) return null;
				switchToNormalMode();
				
			}
			{
			_loop361:
			do {
				if ((LA(1)==CONTRACTS)) {
					contracts();
				}
				else {
					break _loop361;
				}
				
			} while (true);
			}
			{
			_loop363:
			do {
				if ((LA(1)==INVARIANTS)) {
					invariants();
				}
				else {
					break _loop363;
				}
				
			} while (true);
			}
			{
			_loop368:
			do {
				if ((LA(1)==RULES)) {
					match(RULES);
					{
					switch ( LA(1)) {
					case LPAREN:
					{
						choices=option_list(choices);
						break;
					}
					case LBRACE:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(LT(1), getFilename());
					}
					}
					}
					match(LBRACE);
					if ( inputState.guessing==0 ) {
						
						switchToSchemaMode(); 
						
					}
					{
					_loop367:
					do {
						if ((LA(1)==IDENT)) {
							s=taclet(choices);
							match(SEMI);
							if ( inputState.guessing==0 ) {
								
								try {
								if (!skip_taclets) {
								taclets = taclets.addUnique(s);
								}
								} catch(de.uka.ilkd.key.collection.NotUniqueException e) {
								semanticError
								("Cannot add taclet \"" + s.name() + 
								"\" to rule base as a taclet with the same "+
								"name already exists.");
								}
								
							}
						}
						else {
							break _loop367;
						}
						
					} while (true);
					}
					match(RBRACE);
					if ( inputState.guessing==0 ) {
						choices=DefaultImmutableSet.<Choice>nil();
					}
				}
				else {
					break _loop368;
				}
				
			} while (true);
			}
			{
			switch ( LA(1)) {
			case PROBLEM:
			{
				{
				match(PROBLEM);
				match(LBRACE);
				if ( inputState.guessing==0 ) {
					switchToNormalMode(); 
						     if (capturer != null) capturer.capture();
				}
				a=formula();
				match(RBRACE);
				}
				break;
			}
			case CHOOSECONTRACT:
			{
				match(CHOOSECONTRACT);
				{
				switch ( LA(1)) {
				case STRING_LITERAL:
				{
					chooseContract=string_literal();
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
				if ( inputState.guessing==0 ) {
					
						       if (capturer != null) {
						            capturer.capture();
						       }
						       if(chooseContract == null) {
						           chooseContract = "";
						       }
					
				}
				break;
			}
			case PROOFOBLIGATION:
			{
				match(PROOFOBLIGATION);
				{
				switch ( LA(1)) {
				case STRING_LITERAL:
				{
					proofObligation=string_literal();
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
				if ( inputState.guessing==0 ) {
					
					if (capturer != null) {
					capturer.capture();
					}
					if(proofObligation == null) {
					proofObligation = "";
					}
					
				}
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
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
		return a;
	}
	
	public final String  preferences() throws RecognitionException, TokenStreamException {
		String s = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case KEYSETTINGS:
			{
				match(KEYSETTINGS);
				match(LBRACE);
				{
				switch ( LA(1)) {
				case STRING_LITERAL:
				{
					s=string_literal();
					break;
				}
				case RBRACE:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(LT(1), getFilename());
				}
				}
				}
				match(RBRACE);
				break;
			}
			case EOF:
			case SORTS:
			case SCHEMAVARIABLES:
			case PROGRAMVARIABLES:
			case INCLUDE:
			case INCLUDELDTS:
			case CLASSPATH:
			case BOOTCLASSPATH:
			case NODEFAULTCLASSES:
			case JAVASOURCE:
			case WITHOPTIONS:
			case OPTIONSDECL:
			case HEURISTICSDECL:
			case PREDICATES:
			case FUNCTIONS:
			case RULES:
			case PROBLEM:
			case CHOOSECONTRACT:
			case PROOFOBLIGATION:
			case CONTRACTS:
			case INVARIANTS:
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
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_53);
			} else {
			  throw ex;
			}
		}
		return s;
	}
	
	public final String  bootClassPath() throws RecognitionException, TokenStreamException {
		String id = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case BOOTCLASSPATH:
			{
				match(BOOTCLASSPATH);
				id=string_literal();
				match(SEMI);
				break;
			}
			case EOF:
			case SORTS:
			case SCHEMAVARIABLES:
			case PROGRAMVARIABLES:
			case INCLUDE:
			case INCLUDELDTS:
			case CLASSPATH:
			case NODEFAULTCLASSES:
			case JAVASOURCE:
			case WITHOPTIONS:
			case OPTIONSDECL:
			case HEURISTICSDECL:
			case PREDICATES:
			case FUNCTIONS:
			case RULES:
			case PROBLEM:
			case CHOOSECONTRACT:
			case PROOFOBLIGATION:
			case CONTRACTS:
			case INVARIANTS:
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
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_54);
			} else {
			  throw ex;
			}
		}
		return id;
	}
	
	public final ImmutableList<String>  classPaths() throws RecognitionException, TokenStreamException {
		ImmutableList<String> ids = ImmutableSLList.<String>nil();
		
		
		String s = null;
		
		
		try {      // for error handling
			{
			_loop379:
			do {
				switch ( LA(1)) {
				case CLASSPATH:
				{
					{
					match(CLASSPATH);
					s=string_literal();
					if ( inputState.guessing==0 ) {
						
						ids = ids.append(s);
						
					}
					match(SEMI);
					}
					break;
				}
				case NODEFAULTCLASSES:
				{
					{
					match(NODEFAULTCLASSES);
					if ( inputState.guessing==0 ) {
						
						throw new RecognitionException("\\noDefaultClasses is no longer supported. Use \\bootclasspath. See docs/README.classpath");
						
					}
					match(SEMI);
					}
					break;
				}
				default:
				{
					break _loop379;
				}
				}
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_55);
			} else {
			  throw ex;
			}
		}
		return ids;
	}
	
	public final String  javaSource() throws RecognitionException, TokenStreamException {
		String result = null;
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case JAVASOURCE:
			{
				match(JAVASOURCE);
				result=oneJavaSource();
				match(SEMI);
				break;
			}
			case EOF:
			case SORTS:
			case SCHEMAVARIABLES:
			case PROGRAMVARIABLES:
			case INCLUDE:
			case INCLUDELDTS:
			case WITHOPTIONS:
			case OPTIONSDECL:
			case HEURISTICSDECL:
			case PREDICATES:
			case FUNCTIONS:
			case RULES:
			case PROBLEM:
			case CHOOSECONTRACT:
			case PROOFOBLIGATION:
			case CONTRACTS:
			case INVARIANTS:
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
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_3);
			} else {
			  throw ex;
			}
		}
		return result;
	}
	
	public final String  oneJavaSource() throws RecognitionException, TokenStreamException {
		String s = null;
		
		
		StringBuffer b=new StringBuffer();
		String l = null;
		
		
		try {      // for error handling
			{
			int _cnt384=0;
			_loop384:
			do {
				switch ( LA(1)) {
				case STRING_LITERAL:
				{
					l=string_literal();
					if ( inputState.guessing==0 ) {
						
						b.append(l);
						
					}
					break;
				}
				case SLASH:
				{
					match(SLASH);
					if ( inputState.guessing==0 ) {
						b.append("/");
					}
					break;
				}
				default:
				{
					if ( _cnt384>=1 ) { break _loop384; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				}
				_cnt384++;
			} while (true);
			}
			if ( inputState.guessing==0 ) {
				
				s = b.toString();
				
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
		return s;
	}
	
	public final void proof(
		IProofFileParser prl
	) throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			{
			switch ( LA(1)) {
			case PROOF:
			{
				match(PROOF);
				proofBody(prl);
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
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void proofBody(
		IProofFileParser prl
	) throws RecognitionException, TokenStreamException {
		
		
		try {      // for error handling
			match(LBRACE);
			{
			int _cnt392=0;
			_loop392:
			do {
				if ((LA(1)==LPAREN)) {
					pseudosexpr(prl);
				}
				else {
					if ( _cnt392>=1 ) { break _loop392; } else {throw new NoViableAltException(LT(1), getFilename());}
				}
				
				_cnt392++;
			} while (true);
			}
			match(RBRACE);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_0);
			} else {
			  throw ex;
			}
		}
	}
	
	public final void pseudosexpr(
		IProofFileParser prl
	) throws RecognitionException, TokenStreamException {
		
		char eid='0'; String str = "";
		
		try {      // for error handling
			match(LPAREN);
			{
			switch ( LA(1)) {
			case IDENT:
			{
				eid=expreid();
				{
				switch ( LA(1)) {
				case STRING_LITERAL:
				{
					str=string_literal();
					break;
				}
				case LPAREN:
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
				if ( inputState.guessing==0 ) {
					prl.beginExpr(eid,str);
				}
				{
				_loop397:
				do {
					if ((LA(1)==LPAREN)) {
						pseudosexpr(prl);
					}
					else {
						break _loop397;
					}
					
				} while (true);
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
			if ( inputState.guessing==0 ) {
				prl.endExpr(eid, stringLiteralLine);
			}
			match(RPAREN);
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_56);
			} else {
			  throw ex;
			}
		}
	}
	
	public final char  expreid() throws RecognitionException, TokenStreamException {
		 char eid = '0' ;
		
		String id = null;
		
		try {      // for error handling
			id=simple_ident();
			if ( inputState.guessing==0 ) {
				
				Character c = prooflabel2tag.get(id);
				if(c != null)
				eid = c.charValue();
				
			}
		}
		catch (RecognitionException ex) {
			if (inputState.guessing==0) {
				reportError(ex);
				recover(ex,_tokenSet_57);
			} else {
			  throw ex;
			}
		}
		return eid;
	}
	
	
	public static final String[] _tokenNames = {
		"<0>",
		"EOF",
		"<2>",
		"NULL_TREE_LOOKAHEAD",
		"\"\\\\sorts\"",
		"\"\\\\generic\"",
		"\"\\\\extends\"",
		"\"\\\\oneof\"",
		"\"\\\\abstract\"",
		"\"\\\\schemaVariables\"",
		"\"\\\\schemaVar\"",
		"\"\\\\modalOperator\"",
		"\"\\\\program\"",
		"\"\\\\formula\"",
		"\"\\\\term\"",
		"\"\\\\update\"",
		"\"\\\\variables\"",
		"\"\\\\skolemTerm\"",
		"\"\\\\skolemFormula\"",
		"\"\\\\modifies\"",
		"\"\\\\programVariables\"",
		"\"\\\\varcond\"",
		"\"\\\\applyUpdateOnRigid\"",
		"\"\\\\dependingOn\"",
		"\"\\\\disjointModuloNull\"",
		"\"\\\\dropEffectlessElementaries\"",
		"\"\\\\dropEffectlessStores\"",
		"\"\\\\simplifyIfThenElseUpdate\"",
		"\"\\\\enumConstant\"",
		"\"\\\\freeLabelIn\"",
		"\"\\\\hasSort\"",
		"\"\\\\fieldType\"",
		"\"\\\\elemSort\"",
		"\"\\\\isArray\"",
		"\"\\\\isArrayLength\"",
		"\"\\\\isEnumType\"",
		"\"\\\\isInductVar\"",
		"\"\\\\isLocalVariable\"",
		"\"\\\\isObserver\"",
		"\"\\\\different\"",
		"\"\\\\metaDisjoint\"",
		"\"\\\\isReference\"",
		"\"\\\\isReferenceArray\"",
		"\"\\\\sub\"",
		"\"\\\\equalUnique\"",
		"\"\\\\new\"",
		"\"\\\\newLabel\"",
		"\"\\\\not\"",
		"\"\\\\notFreeIn\"",
		"\"\\\\same\"",
		"\"\\\\static\"",
		"\"\\\\staticMethodReference\"",
		"\"\\\\strict\"",
		"\"\\\\typeof\"",
		"\"\\\\instantiateGeneric\"",
		"\"\\\\forall\"",
		"\"\\\\exists\"",
		"\"\\\\subst\"",
		"\"\\\\if\"",
		"\"\\\\ifEx\"",
		"\"\\\\then\"",
		"\"\\\\else\"",
		"\"\\\\include\"",
		"\"\\\\includeLDTs\"",
		"\"\\\\classpath\"",
		"\"\\\\bootclasspath\"",
		"\"\\\\noDefaultClasses\"",
		"\"\\\\javaSource\"",
		"\"\\\\withOptions\"",
		"\"\\\\optionsDecl\"",
		"\"\\\\settings\"",
		"\"true\"",
		"\"false\"",
		"\"\\\\sameUpdateLevel\"",
		"\"\\\\inSequentState\"",
		"\"\\\\antecedentPolarity\"",
		"\"\\\\succedentPolarity\"",
		"\"\\\\closegoal\"",
		"\"\\\\heuristicsDecl\"",
		"\"\\\\noninteractive\"",
		"\"\\\\displayname\"",
		"\"\\\\helptext\"",
		"\"\\\\replacewith\"",
		"\"\\\\addrules\"",
		"\"\\\\addprogvars\"",
		"\"\\\\heuristics\"",
		"\"\\\\find\"",
		"\"\\\\add\"",
		"\"\\\\assumes\"",
		"\"\\\\predicates\"",
		"\"\\\\functions\"",
		"\"\\\\unique\"",
		"\"\\\\rules\"",
		"\"\\\\problem\"",
		"\"\\\\chooseContract\"",
		"\"\\\\proofObligation\"",
		"\"\\\\proof\"",
		"\"\\\\contracts\"",
		"\"\\\\invariants\"",
		"\"\\\\inType\"",
		"\"\\\\isAbstractOrInterface\"",
		"\"\\\\containerType\"",
		"\"$lmtd\"",
		"\"\\\\locset\"",
		"\"\\\\seq\"",
		"\"\\\\bigint\"",
		"VOCAB",
		"`;'",
		"`/'",
		"`:'",
		"Double `:'",
		"`:='",
		"`.'",
		"`..'",
		"`,'",
		"`('",
		"`)'",
		"`{'",
		"`}'",
		"`['",
		"']'",
		"a pair of empty brackets []",
		"`at'",
		"`parallel'",
		"`|'",
		"`&'",
		"`->'",
		"`='",
		"`!='",
		"`==>'",
		"'^'",
		"'~'",
		"`%'",
		"`*'",
		"`-'",
		"`+'",
		"`>'",
		"`>='",
		"`>>'",
		"white space",
		"a string in double quotes",
		"LESS_DISPATCH",
		"'<'",
		"'<='",
		"'<<'",
		"an implicit identifier (letters only)",
		"`<->'",
		"PRIMES_OR_CHARLITERAL",
		"Sequence of primes (at least one)",
		"a char in single quotes",
		"ESC",
		"a string with double quotes",
		"a comment",
		"a comment",
		"DIGIT_DISPATCH",
		"a hexadeciaml constant",
		"a digit",
		"a hexadeciamal number",
		"a letter",
		"an admissible character for identifiers",
		"an identifer",
		"a number",
		"All possible modalities, including schema.",
		"MODALITYEND",
		"JAVABLOCK"
	};
	
	private static final long[] mk_tokenSet_0() {
		long[] data = { 2L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = { 524290L, 18014398509547520L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	private static final long[] mk_tokenSet_2() {
		long[] data = { 2L, 29796335616L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_2 = new BitSet(mk_tokenSet_2());
	private static final long[] mk_tokenSet_3() {
		long[] data = { -4611686018426338798L, 29897015344L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_3 = new BitSet(mk_tokenSet_3());
	private static final long[] mk_tokenSet_4() {
		long[] data = { 1049106L, 29897015328L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_4 = new BitSet(mk_tokenSet_4());
	private static final long[] mk_tokenSet_5() {
		long[] data = { 972918257001431570L, 299489405117153696L, 30066872384L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_5 = new BitSet(mk_tokenSet_5());
	private static final long[] mk_tokenSet_6() {
		long[] data = { 0L, 1134695999864832L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_6 = new BitSet(mk_tokenSet_6());
	private static final long[] mk_tokenSet_7() {
		long[] data = { 0L, 25957270510862336L, 4096L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_7 = new BitSet(mk_tokenSet_7());
	private static final long[] mk_tokenSet_8() {
		long[] data = { 0L, 8796093022208L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_8 = new BitSet(mk_tokenSet_8());
	private static final long[] mk_tokenSet_9() {
		long[] data = { 0L, 19140298416324608L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_9 = new BitSet(mk_tokenSet_9());
	private static final long[] mk_tokenSet_10() {
		long[] data = { 288L, 18014398509481984L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_10 = new BitSet(mk_tokenSet_10());
	private static final long[] mk_tokenSet_11() {
		long[] data = { 192L, 94584388267802624L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_11 = new BitSet(mk_tokenSet_11());
	private static final long[] mk_tokenSet_12() {
		long[] data = { 64L, 8796093022208L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_12 = new BitSet(mk_tokenSet_12());
	private static final long[] mk_tokenSet_13() {
		long[] data = { 66L, 239895844994678784L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_13 = new BitSet(mk_tokenSet_13());
	private static final long[] mk_tokenSet_14() {
		long[] data = { 524482L, -43705587138560L, 4295349235L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_14 = new BitSet(mk_tokenSet_14());
	private static final long[] mk_tokenSet_15() {
		long[] data = { 0L, 5638295627235328L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_15 = new BitSet(mk_tokenSet_15());
	private static final long[] mk_tokenSet_16() {
		long[] data = { 2L, 23643898043695104L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_16 = new BitSet(mk_tokenSet_16());
	private static final long[] mk_tokenSet_17() {
		long[] data = { 0L, 4503599627370496L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_17 = new BitSet(mk_tokenSet_17());
	private static final long[] mk_tokenSet_18() {
		long[] data = { 2620416L, 20266198353321984L, 4096L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_18 = new BitSet(mk_tokenSet_18());
	private static final long[] mk_tokenSet_19() {
		long[] data = { 0L, 0L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_19 = new BitSet(mk_tokenSet_19());
	private static final long[] mk_tokenSet_20() {
		long[] data = { 0L, 18014398509481984L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_20 = new BitSet(mk_tokenSet_20());
	private static final long[] mk_tokenSet_21() {
		long[] data = { 524290L, -432459638558883840L, 377843L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_21 = new BitSet(mk_tokenSet_21());
	private static final long[] mk_tokenSet_22() {
		long[] data = { 0L, 2260595906707456L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_22 = new BitSet(mk_tokenSet_22());
	private static final long[] mk_tokenSet_23() {
		long[] data = { 0L, 18014398643699712L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_23 = new BitSet(mk_tokenSet_23());
	private static final long[] mk_tokenSet_24() {
		long[] data = { 2L, 167759086119550976L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_24 = new BitSet(mk_tokenSet_24());
	private static final long[] mk_tokenSet_25() {
		long[] data = { 2L, 23652694136717312L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_25 = new BitSet(mk_tokenSet_25());
	private static final long[] mk_tokenSet_26() {
		long[] data = { 2L, 167767882212573184L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_26 = new BitSet(mk_tokenSet_26());
	private static final long[] mk_tokenSet_27() {
		long[] data = { 2L, 167838250956750848L, 4294967296L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_27 = new BitSet(mk_tokenSet_27());
	private static final long[] mk_tokenSet_28() {
		long[] data = { 524290L, -443727708598239232L, 312307L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_28 = new BitSet(mk_tokenSet_28());
	private static final long[] mk_tokenSet_29() {
		long[] data = { 0L, 70368744177664L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_29 = new BitSet(mk_tokenSet_29());
	private static final long[] mk_tokenSet_30() {
		long[] data = { 524290L, 8670695920083468288L, 262146L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_30 = new BitSet(mk_tokenSet_30());
	private static final long[] mk_tokenSet_31() {
		long[] data = { 864691128455135232L, 299489375220138368L, 12887003200L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_31 = new BitSet(mk_tokenSet_31());
	private static final long[] mk_tokenSet_32() {
		long[] data = { 524290L, -480037980593913856L, 312307L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_32 = new BitSet(mk_tokenSet_32());
	private static final long[] mk_tokenSet_33() {
		long[] data = { 864691128455135232L, 290482175965397376L, 12887003200L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_33 = new BitSet(mk_tokenSet_33());
	private static final long[] mk_tokenSet_34() {
		long[] data = { 524290L, -441475908784553984L, 312307L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_34 = new BitSet(mk_tokenSet_34());
	private static final long[] mk_tokenSet_35() {
		long[] data = { 524290L, -443727708598239232L, 377843L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_35 = new BitSet(mk_tokenSet_35());
	private static final long[] mk_tokenSet_36() {
		long[] data = { 0L, 288230376151711744L, 12886999104L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_36 = new BitSet(mk_tokenSet_36());
	private static final long[] mk_tokenSet_37() {
		long[] data = { 0L, 0L, 1024L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_37 = new BitSet(mk_tokenSet_37());
	private static final long[] mk_tokenSet_38() {
		long[] data = { 972918257000382464L, 317503773729620352L, 30066872384L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_38 = new BitSet(mk_tokenSet_38());
	private static final long[] mk_tokenSet_39() {
		long[] data = { 972918257000382464L, 299489375220138368L, 30066872384L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_39 = new BitSet(mk_tokenSet_39());
	private static final long[] mk_tokenSet_40() {
		long[] data = { 0L, 5629499534213120L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_40 = new BitSet(mk_tokenSet_40());
	private static final long[] mk_tokenSet_41() {
		long[] data = { 0L, 5638295627235328L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_41 = new BitSet(mk_tokenSet_41());
	private static final long[] mk_tokenSet_42() {
		long[] data = { 0L, 4503599627370496L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_42 = new BitSet(mk_tokenSet_42());
	private static final long[] mk_tokenSet_43() {
		long[] data = { 0L, 9007199254740992L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_43 = new BitSet(mk_tokenSet_43());
	private static final long[] mk_tokenSet_44() {
		long[] data = { 0L, 18014398511808512L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_44 = new BitSet(mk_tokenSet_44());
	private static final long[] mk_tokenSet_45() {
		long[] data = { 0L, 18014398509481984L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_45 = new BitSet(mk_tokenSet_45());
	private static final long[] mk_tokenSet_46() {
		long[] data = { 0L, 4503599627370496L, 2L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_46 = new BitSet(mk_tokenSet_46());
	private static final long[] mk_tokenSet_47() {
		long[] data = { 0L, 18023194604830720L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_47 = new BitSet(mk_tokenSet_47());
	private static final long[] mk_tokenSet_48() {
		long[] data = { 0L, 18023194614792192L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_48 = new BitSet(mk_tokenSet_48());
	private static final long[] mk_tokenSet_49() {
		long[] data = { 0L, 18023194606403584L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_49 = new BitSet(mk_tokenSet_49());
	private static final long[] mk_tokenSet_50() {
		long[] data = { 0L, 18023194605879296L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_50 = new BitSet(mk_tokenSet_50());
	private static final long[] mk_tokenSet_51() {
		long[] data = { 524290L, -441475908784553984L, 377843L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_51 = new BitSet(mk_tokenSet_51());
	private static final long[] mk_tokenSet_52() {
		long[] data = { 2L, 21206401024L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_52 = new BitSet(mk_tokenSet_52());
	private static final long[] mk_tokenSet_53() {
		long[] data = { -4611686018426338798L, 29897015359L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_53 = new BitSet(mk_tokenSet_53());
	private static final long[] mk_tokenSet_54() {
		long[] data = { -4611686018426338798L, 29897015357L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_54 = new BitSet(mk_tokenSet_54());
	private static final long[] mk_tokenSet_55() {
		long[] data = { -4611686018426338798L, 29897015352L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_55 = new BitSet(mk_tokenSet_55());
	private static final long[] mk_tokenSet_56() {
		long[] data = { 0L, 24769797950537728L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_56 = new BitSet(mk_tokenSet_56());
	private static final long[] mk_tokenSet_57() {
		long[] data = { 0L, 6755399441055744L, 4096L, 0L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_57 = new BitSet(mk_tokenSet_57());
	
	}
