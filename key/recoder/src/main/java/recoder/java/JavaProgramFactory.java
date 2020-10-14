// This file is part of the RECODER library and protected by the LGPL

package recoder.java;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.io.StringWriter;
import java.io.Writer;
import java.nio.CharBuffer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import recoder.DefaultServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.convenience.TreeWalker;
import recoder.io.ProjectSettings;
import recoder.io.PropertyNames;
import recoder.java.SourceElement.Position;
import recoder.java.declaration.AnnotationDeclaration;
import recoder.java.declaration.AnnotationPropertyDeclaration;
import recoder.java.declaration.AnnotationUseSpecification;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.ClassInitializer;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.declaration.Extends;
import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.FieldSpecification;
import recoder.java.declaration.Implements;
import recoder.java.declaration.InterfaceDeclaration;
import recoder.java.declaration.LocalVariableDeclaration;
import recoder.java.declaration.MemberDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.declaration.Throws;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.java.declaration.modifier.Abstract;
import recoder.java.declaration.modifier.Final;
import recoder.java.declaration.modifier.Native;
import recoder.java.declaration.modifier.Private;
import recoder.java.declaration.modifier.Protected;
import recoder.java.declaration.modifier.Public;
import recoder.java.declaration.modifier.Static;
import recoder.java.declaration.modifier.StrictFp;
import recoder.java.declaration.modifier.Synchronized;
import recoder.java.declaration.modifier.Transient;
import recoder.java.declaration.modifier.VisibilityModifier;
import recoder.java.declaration.modifier.Volatile;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.expression.literal.BooleanLiteral;
import recoder.java.expression.literal.CharLiteral;
import recoder.java.expression.literal.DoubleLiteral;
import recoder.java.expression.literal.FloatLiteral;
import recoder.java.expression.literal.IntLiteral;
import recoder.java.expression.literal.LongLiteral;
import recoder.java.expression.literal.NullLiteral;
import recoder.java.expression.literal.StringLiteral;
import recoder.java.expression.operator.BinaryAnd;
import recoder.java.expression.operator.BinaryAndAssignment;
import recoder.java.expression.operator.BinaryNot;
import recoder.java.expression.operator.BinaryOr;
import recoder.java.expression.operator.BinaryOrAssignment;
import recoder.java.expression.operator.BinaryXOr;
import recoder.java.expression.operator.BinaryXOrAssignment;
import recoder.java.expression.operator.Conditional;
import recoder.java.expression.operator.CopyAssignment;
import recoder.java.expression.operator.Divide;
import recoder.java.expression.operator.DivideAssignment;
import recoder.java.expression.operator.Equals;
import recoder.java.expression.operator.GreaterOrEquals;
import recoder.java.expression.operator.GreaterThan;
import recoder.java.expression.operator.Instanceof;
import recoder.java.expression.operator.LessOrEquals;
import recoder.java.expression.operator.LessThan;
import recoder.java.expression.operator.LogicalAnd;
import recoder.java.expression.operator.LogicalNot;
import recoder.java.expression.operator.LogicalOr;
import recoder.java.expression.operator.Minus;
import recoder.java.expression.operator.MinusAssignment;
import recoder.java.expression.operator.Modulo;
import recoder.java.expression.operator.ModuloAssignment;
import recoder.java.expression.operator.Negative;
import recoder.java.expression.operator.New;
import recoder.java.expression.operator.NewArray;
import recoder.java.expression.operator.NotEquals;
import recoder.java.expression.operator.Plus;
import recoder.java.expression.operator.PlusAssignment;
import recoder.java.expression.operator.Positive;
import recoder.java.expression.operator.PostDecrement;
import recoder.java.expression.operator.PostIncrement;
import recoder.java.expression.operator.PreDecrement;
import recoder.java.expression.operator.PreIncrement;
import recoder.java.expression.operator.ShiftLeft;
import recoder.java.expression.operator.ShiftLeftAssignment;
import recoder.java.expression.operator.ShiftRight;
import recoder.java.expression.operator.ShiftRightAssignment;
import recoder.java.expression.operator.Times;
import recoder.java.expression.operator.TimesAssignment;
import recoder.java.expression.operator.TypeCast;
import recoder.java.expression.operator.UnsignedShiftRight;
import recoder.java.expression.operator.UnsignedShiftRightAssignment;
import recoder.java.reference.AnnotationPropertyReference;
import recoder.java.reference.ArrayReference;
import recoder.java.reference.FieldReference;
import recoder.java.reference.MetaClassReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.PackageReference;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.SuperConstructorReference;
import recoder.java.reference.SuperReference;
import recoder.java.reference.ThisConstructorReference;
import recoder.java.reference.ThisReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.java.reference.VariableReference;
import recoder.java.statement.Assert;
import recoder.java.statement.Branch;
import recoder.java.statement.Break;
import recoder.java.statement.Case;
import recoder.java.statement.Catch;
import recoder.java.statement.Continue;
import recoder.java.statement.Default;
import recoder.java.statement.Do;
import recoder.java.statement.Else;
import recoder.java.statement.EmptyStatement;
import recoder.java.statement.EnhancedFor;
import recoder.java.statement.Finally;
import recoder.java.statement.For;
import recoder.java.statement.If;
import recoder.java.statement.LabeledStatement;
import recoder.java.statement.Return;
import recoder.java.statement.Switch;
import recoder.java.statement.SynchronizedBlock;
import recoder.java.statement.Then;
import recoder.java.statement.Throw;
import recoder.java.statement.Try;
import recoder.java.statement.While;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.parser.JavaCCParser;
import recoder.util.StringUtils;

public class JavaProgramFactory implements ProgramFactory, PropertyChangeListener {

    /**
     * Private constructor - use {@link #getInstance}instead.
     */
    private JavaProgramFactory() { /* singleton */
    }
    
    public static class TraceItem {
    	public final ProgramElement pe;
    	public final String st;
    	public TraceItem(ProgramElement pe) {
    		this.pe = pe;
    		StackTraceElement[] ste = new Throwable().getStackTrace();
    		int startIdx = 3;
    		while (ste[startIdx].toString().indexOf("<init>") != -1
    				|| ste[startIdx].toString().indexOf(".deepClone(") != -1)
    			startIdx++;
    		st = "\t"+ste[startIdx+0]+"\n\t"+ste[startIdx+1]+"\n\t"+ste[startIdx+2];
    	}
    	@Override
    	public boolean equals(Object o) {
    		if (o == pe)
    			return true; // TODO 0.90 hack!!
    		if (!(o instanceof TraceItem))
    			return false;
    		return ((TraceItem)o).pe == pe;
    	}
    	@Override
    	public int hashCode() {
    		return pe.hashCode();
    	}
    	@Override
    	public String toString() {
    		return pe.toString() + "\n" + st;
    	}
    }
    
    private HashMap<ProgramElement, TraceItem> createdItems;
    private boolean doTrace = false;
    private boolean autoTrace = true; // TODO...
    /**
     * debug method
     * @since 0.90
     */
    public void beginTracing() {
    	createdItems = new HashMap<ProgramElement, TraceItem>(1000);
    	doTrace = true;
    }
    
    public void detrace(ProgramElement pe) {
    	TreeWalker tw = new TreeWalker(pe);
    	while (tw.next()) {
    		createdItems.remove(tw.getProgramElement());
    	}
    }
    
    public TraceItem getTraceItem(ProgramElement pe) {
    	return createdItems.get(pe);
    }
    

    /**
     * debug method
     * @since 0.90
     */
    public Collection<TraceItem> endTracing() {
    	doTrace = false;
    	return createdItems.values();
    }
    
    // only to be called from JavaSourceElement prototype-constructor and internally!!
    public void trace(ProgramElement pe) {
    	if (doTrace && autoTrace) {
    		createdItems.put(pe, new TraceItem(pe));
    	}
    }
    
    public void manTrace(ProgramElement pe) {
    	if (doTrace)
    		createdItems.put(pe, new TraceItem(pe));
    }

    /**
     * The singleton instance of the program factory.
     */
    private static JavaProgramFactory theFactory = new JavaProgramFactory();

    /**
     * The singleton instance of the program factory.
     */
    private static ServiceConfiguration serviceConfiguration;

    /**
     * StringWriter for toSource.
     */
    private static StringWriter writer = new StringWriter();

    /**
     * PrettyPrinter, for toSource.
     */
    private static PrettyPrinter sourcePrinter;
    
    private static boolean useAddNewlineReader = true;

    /**
     * Called by the service configuration indicating that all services are
     * known. Services may now start communicating or linking among their
     * configuration partners. The service configuration can be memorized if it
     * has not been passed in by a constructor already.
     * 
     * @param cfg
     *            the service configuration this services has been assigned to.
     */
    public void initialize(ServiceConfiguration cfg) {
        serviceConfiguration = cfg;
        
        ProjectSettings settings = serviceConfiguration.getProjectSettings();
        settings.addPropertyChangeListener(this);
        writer = new StringWriter();
        sourcePrinter = new PrettyPrinter(writer, settings.getProperties());
        JavaCCParser.setAwareOfAssert(StringUtils.parseBooleanProperty(settings.getProperties().getProperty(
                PropertyNames.JDK1_4)));
        JavaCCParser.setJava5(StringUtils.parseBooleanProperty(settings.getProperties().getProperty(
                PropertyNames.JAVA_5)));
    }

    /**
     * Returns the service configuration this service is a part of.
     * 
     * @return the configuration of this service.
     */
    public ServiceConfiguration getServiceConfiguration() {
        return serviceConfiguration;
    }

    /**
     * Returns the single instance of this class.
     */
    public static JavaProgramFactory getInstance() {
        return theFactory;
    }

    /**
     * For internal reuse and synchronization.
     */
    private static JavaCCParser parser = new JavaCCParser(System.in);

    private final static Position ZERO_POSITION = new Position(0, 0);
    
    private static void attachComment(Comment c, ProgramElement pe) {
    	ProgramElement dest = pe;

    	if (c.isPrefixed() && pe instanceof CompilationUnit && ((CompilationUnit)pe).getChildCount() > 0) {
    		// may need attach to first child element
    		ProgramElement fc = ((CompilationUnit)pe).getChildAt(0);
    		int distcu = c.getStartPosition().getLine();
    		int distfc = fc.getStartPosition().getLine() - c.getEndPosition().getLine();
    		if (c instanceof SingleLineComment) distcu--;
    		if (distcu >= distfc) {
    			dest = fc; 
    		}
    	}
    	else if (!c.isPrefixed()) {
            NonTerminalProgramElement ppe = dest.getASTParent();
            int i = 0;
            if (ppe != null) {
                while (ppe.getChildAt(i) != dest) i++;
            }
            if (i == 0) { // before syntactical parent
                c.setPrefixed(true);
            } else {
                dest = ppe.getChildAt(i - 1);
                while (dest instanceof NonTerminalProgramElement) {
                    ppe = (NonTerminalProgramElement) dest;
                    i = ppe.getChildCount();
                    if (i == 0) {
                        break;
                    }
                    dest = ppe.getChildAt(i - 1);
                }
                // Comments attached better - Fix by T.Gutzmann
                ppe = dest.getASTParent();
                boolean doChange = false;
                while (ppe != null && ppe.getASTParent() != null
                        && ppe.getEndPosition().compareTo(dest.getEndPosition()) >= 0
                        && ppe.getASTParent().getEndPosition().compareTo(c.getStartPosition()) <= 0) {
                    ppe = ppe.getASTParent();
                    doChange = true;
                }
                if (ppe != null && doChange)
                    dest = ppe;
                if (dest instanceof NonTerminalProgramElement) {
                    ppe = (NonTerminalProgramElement) dest;
                    if (ppe.getEndPosition().compareTo(c.getStartPosition()) >= 0) {
                        while (ppe.getChildCount() > 0
                                && ppe.getChildAt(ppe.getChildCount() - 1).getEndPosition().compareTo(
                                        ppe.getEndPosition()) == 0
                                // TODO Gutzmann - this shouldn't be neccessary
                                && ppe.getChildAt(ppe.getChildCount() - 1) instanceof NonTerminalProgramElement) {
                            ppe = (NonTerminalProgramElement) ppe.getChildAt(ppe.getChildCount() - 1);
                            dest = ppe;
                        }
                        c.setContainerComment(true);
                    }
                }
                if (!c.isContainerComment() && pe != dest) {
                    // if in between two program elements in same line, prefer prefixing/look at number of whitespaces
                    if (pe.getFirstElement().getStartPosition().getLine() == dest.getLastElement().getEndPosition().getLine()) {
                        // TODO strategy when looking at # of whitespaces ?!
                        int before = c.getStartPosition().getColumn() - dest.getLastElement().getEndPosition().getColumn();
                        int after = pe.getFirstElement().getStartPosition().getColumn() - c.getEndPosition().getColumn();
                        if (after <= before) {
                            dest = pe;
                            c.setPrefixed(true);
                        }
                    }
                }
            }
        }
    	if (c.isPrefixed()) {
    		// once again, go up as long as possible
    		NonTerminalProgramElement npe = dest.getASTParent();
    		while (npe != null && npe.getStartPosition().equals(dest.getStartPosition())) {
    			dest = npe;
    			npe = npe.getASTParent();
    		}
    	} else {
    		NonTerminalProgramElement npe = dest.getASTParent();
    		while (npe != null && npe.getEndPosition().equals(dest.getEndPosition())) {
    			dest = npe;
    			npe = npe.getASTParent();
    		}
    	}
    	// if this is a full line comment, may need to change
    	if (c.isPrefixed() && c.getEndPosition().getLine() <  dest.getStartPosition().getLine()) {
    		NonTerminalProgramElement npe = dest.getASTParent();
    		if (npe != null) {
    			int idx = npe.getIndexOfChild(dest);
    			if (idx > 0) {
    				// calculate distance, maybe attach to next element
    				int distPre = dest.getStartPosition().getLine() - c.getEndPosition().getLine();
    				int distPost = c.getStartPosition().getLine() - npe.getChildAt(idx-1).getEndPosition().getLine();
    				if (c instanceof SingleLineComment)
    					distPost--; // prefer postfix comment in this case
    				if (distPost < distPre) {
    					dest = npe.getChildAt(idx-1);
    					c.setPrefixed(false);
    				}
    			}
    		}
    	} else if (!c.isPrefixed() && c.getStartPosition().getLine() > dest.getEndPosition().getLine()) {
    		NonTerminalProgramElement npe = dest.getASTParent();
    		if (npe != null) {
    			int idx = npe.getIndexOfChild(dest);
    			if (idx+1 < npe.getChildCount()) {
    				int distPre = npe.getChildAt(idx+1).getStartPosition().getLine() - c.getEndPosition().getLine();
    				int distPost = c.getStartPosition().getLine() - dest.getEndPosition().getLine();
    				if (c instanceof SingleLineComment)
    					distPost--;
    				if (distPre <= distPost) {
    					dest = npe.getChildAt(idx+1);
    					c.setPrefixed(true);
    				}
    			}
    		}
    	}
    	
        if (c instanceof SingleLineComment && c.isPrefixed()) {
            Position p = dest.getFirstElement().getRelativePosition();
            if (p.getLine() < 1) {
                p.setLine(1);
                dest.getFirstElement().setRelativePosition(p);
            }
        }
        ASTList<Comment> cml = dest.getComments();
        if (cml == null) {
            dest.setComments(cml = new ASTArrayList<Comment>());
        }
        cml.add(c);
    }

    /**
     * Perform post work on the created element. Creates parent links and
     * assigns comments.
     */
    private static void postWork(ProgramElement pe) {

    	List<Comment> comments = JavaCCParser.getComments();
        int commentIndex = 0;
        int commentCount = comments.size();
        Position cpos = ZERO_POSITION;
        Comment current = null;
        if (commentIndex < commentCount) {
            current = comments.get(commentIndex);
            cpos = current.getFirstElement().getStartPosition();
        }
        TreeWalker tw = new TreeWalker(pe);
        while (tw.next()) {
            pe = tw.getProgramElement();
            if (pe instanceof NonTerminalProgramElement) {
                ((NonTerminalProgramElement) pe).makeParentRoleValid();
            }
            Position pos = pe.getFirstElement().getStartPosition();
            while ((commentIndex < commentCount) && pos.compareTo(cpos) > 0) {
                attachComment(current, pe);
                commentIndex += 1;
                if (commentIndex < commentCount) {
                    current = comments.get(commentIndex);
                    cpos = current.getFirstElement().getStartPosition();
                }
            }
        }
        if (commentIndex < commentCount) {
            while (pe.getASTParent() != null) {
                pe = pe.getASTParent();
            }

            /*
             * postfixed comments may need to be attached to a child of current
             * program element, so move down AST while child is closer to comment
             * position.
             */
            do {
                current = comments.get(commentIndex);
                ProgramElement dest = pe;
                ProgramElement newDest = null;
                while (dest instanceof NonTerminalProgramElement) {
                    NonTerminalProgramElement npe = (NonTerminalProgramElement) dest;
                    if (npe.getChildCount() == 0)
                        break;
                    newDest = npe.getChildAt(npe.getChildCount() - 1);
                    if ((npe.getEndPosition().compareTo(current.getStartPosition()) > 0 || ((npe.getEndPosition()
                            .compareTo(current.getStartPosition()) == 0) && newDest.getEndPosition().compareTo(
                            current.getStartPosition()) <= 0))
                            && dest != newDest)
                        dest = newDest;
                    else
                        break;
                }
                ASTList<Comment> cml = dest.getComments();
                if (cml == null) {
                    dest.setComments(cml = new ASTArrayList<Comment>());
                }
                current.setPrefixed(false);
                cml.add(current);
                commentIndex += 1;
            } while (commentIndex < commentCount);
        }
    }
    
    private class AddNewlineReader extends Reader {
    	private Reader reader;
    	AddNewlineReader(Reader reader) {
    		this.reader = reader;
    	}
    	@Override
		public void mark(int readAheadLimit) throws IOException {
			reader.mark(readAheadLimit);
		}
		@Override
		public boolean markSupported() {
			return reader.markSupported();
		}
		@Override
		public int read() throws IOException {
			return reader.read();
		}
		@Override
		public int read(char[] cbuf) throws IOException {
			return reader.read(cbuf);
		}
		@Override
		public int read(CharBuffer target) throws IOException {
			return reader.read(target);
		}
		@Override
		public boolean ready() throws IOException {
			return reader.ready();
		}
		@Override
		public void reset() throws IOException {
			reader.reset();
		}
		@Override
		public long skip(long n) throws IOException {
			return reader.skip(n);
		}		
		@Override
		public void close() throws IOException {
			reader.close();
		}
		private boolean added = false;
		@Override
		public int read(char[] cbuf, int off, int len) throws IOException {
			if (added) return -1;
			int result = reader.read(cbuf, off, len);
			if (!added && result < len) {
				if (result == -1) result++;
				cbuf[off+result++] = '\n';
				added = true;
			}			
			return result;
		}
    }

    /**
     * Parse a {@link CompilationUnit}from the given reader.
     */
    public CompilationUnit parseCompilationUnit(Reader in) throws IOException, ParserException {
        synchronized 
        (parser) {
            parser.initialize(useAddNewlineReader ? new AddNewlineReader(in) : in);
            CompilationUnit res = parser.CompilationUnit();
            postWork(res);
            return res;
        }
    }
    
    /**
     * Parse a {@link CompilationUnit}from the given reader.
     * The supplied sourceVersion parameter describes the java version.
     * @author NAI
     * 
     * @param in
     * @param sourceVersion allowed values: "1.3", "1.4", "5". Defaults to Java 1.4 behavior if sourceVersion is <code>null</code> or any other string.
     * @return
     * @throws IOException
     * @throws ParserException
     */
    public CompilationUnit parseCompilationUnit(Reader in, String sourceVersion) throws IOException, ParserException {
    	//default java version is java1.4
    	boolean java14=true;
    	boolean java5=false;
    	if(sourceVersion!=null){
    		if(sourceVersion.equals("1.3") || sourceVersion.startsWith("1.3.")){
    			java14=false;
    			java5=false;
    		}
    		if(sourceVersion.equals("1.4") || sourceVersion.startsWith("1.4.")){
    			java14=true;
    			java5=false;
    		}
    		if(sourceVersion.equals("1.5") || sourceVersion.startsWith("1.5.")){
    			java14=true;
    			java5=true;
    		}
    		if(sourceVersion.equals("5") || sourceVersion.startsWith("5.")){
    			java14=true;
    			java5=true;
    		}
    	}
        synchronized 
        (parser) {
        	boolean wasJava14=parser.isAwareOfAssert();
        	boolean wasJava5 =parser.isJava5();
        	
        	parser.setAwareOfAssert(java14);
            parser.setJava5(java5);
            parser.initialize(useAddNewlineReader ? new AddNewlineReader(in) : in);
            CompilationUnit res = parser.CompilationUnit();
            postWork(res);

            parser.setAwareOfAssert(wasJava14);
            parser.setJava5(wasJava5);
                        
            return res;
        }
    }

    /**
     * Parse a {@link TypeDeclaration}from the given reader.
     */
    public TypeDeclaration parseTypeDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            TypeDeclaration res = parser.TypeDeclaration();
            postWork(res);
            return res;
        }
    }
    
    public TypeArgumentDeclaration parseTypeArgumentDeclaration(Reader in) throws IOException, ParserException {
    	synchronized(parser) {
    		parser.initialize(in);
    		TypeArgumentDeclaration res = parser.TypeArgument();
    		postWork(res);
    		return res;
    	}
    }

    /**
     * Parse a {@link FieldDeclaration}from the given reader.
     */
    public FieldDeclaration parseFieldDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            FieldDeclaration res = parser.FieldDeclaration();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link MethodDeclaration}from the given reader.
     */
    public MethodDeclaration parseMethodDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            MethodDeclaration res = parser.MethodDeclaration();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link MemberDeclaration}from the given reader.
     */
    public MemberDeclaration parseMemberDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            MemberDeclaration res = parser.ClassBodyDeclaration();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link ParameterDeclaration}from the given reader.
     */
    public ParameterDeclaration parseParameterDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            ParameterDeclaration res = parser.FormalParameter();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link ConstructorDeclaration}from the given reader.
     */
    public ConstructorDeclaration parseConstructorDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            ConstructorDeclaration res = parser.ConstructorDeclaration();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse a {@link TypeReference}from the given reader.
     */
    public TypeReference parseTypeReference(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            TypeReference res = parser.ResultType();
            postWork(res);
            return res;
        }
    }
    
    public PackageReference parsePackageReference(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            PackageReference res = parser.Name().toPackageReference();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse an {@link Expression}from the given reader.
     */
    public Expression parseExpression(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            Expression res = parser.Expression();
            postWork(res);
            return res;
        }
    }

    /**
     * Parse some {@link Statement}s from the given reader.
     */
    public ASTList<Statement> parseStatements(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            ASTList<Statement> res = parser.GeneralizedStatements();
            for (int i = 0; i < res.size(); i += 1) {
                postWork(res.get(i));
            }
            return res;
        }
    }

    /**
     * Parse a {@link StatementBlock}from the given string.
     */
    public StatementBlock parseStatementBlock(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            parser.initialize(in);
            StatementBlock res = parser.Block();
            postWork(res);
            return res;
        }
    }
    
    /**
     * Parse a {@link CompilationUnit}from the given string.
     */
    public CompilationUnit parseCompilationUnit(String in) throws ParserException {
        try {
            return parseCompilationUnit(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse {@link CompilationUnit}s from the given string.
     */
    public List<CompilationUnit> parseCompilationUnits(String[] ins) throws ParserException {
        try {
        	List<CompilationUnit> cus = new ArrayList<CompilationUnit>();
            for (int i = 0; i < ins.length; i++) {
                CompilationUnit cu = parseCompilationUnit(new FileReader(ins[i]));
                cus.add(cu);
            }
            return cus;
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link TypeDeclaration}from the given string.
     */
    public TypeDeclaration parseTypeDeclaration(String in) throws ParserException {
        try {
            return parseTypeDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link MemberDeclaration}from the given string.
     */
    public MemberDeclaration parseMemberDeclaration(String in) throws ParserException {
        try {
            return parseMemberDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link FieldDeclaration}from the given string.
     */
    public FieldDeclaration parseFieldDeclaration(String in) throws ParserException {
        try {
            return parseFieldDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link MethodDeclaration}from the given string.
     */
    public MethodDeclaration parseMethodDeclaration(String in) throws ParserException {
        try {
            return parseMethodDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link ParameterDeclaration}from the given string.
     */
    public ParameterDeclaration parseParameterDeclaration(String in) throws ParserException {
        try {
            return parseParameterDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link ConstructorDeclaration}from the given string.
     */
    public ConstructorDeclaration parseConstructorDeclaration(String in) throws ParserException {
        try {
            return parseConstructorDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link TypeReference}from the given string.
     */
    public TypeReference parseTypeReference(String in) throws ParserException {
        try {
            return parseTypeReference(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a {@link TypeReference}from the given string.
     */
    public PackageReference parsePackageReference(String in) throws ParserException {
        try {
            return parsePackageReference(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse an {@link Expression}from the given string.
     */
    public Expression parseExpression(String in) throws ParserException {
        try {
            return parseExpression(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }

    /**
     * Parse a list of {@link Statement}s from the given string.
     */
    public ASTList<Statement> parseStatements(String in) throws ParserException {
        try {
            return parseStatements(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }
    
    public StatementBlock parseStatementBlock(String in) throws ParserException {
        try {
            return parseStatementBlock(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException(("" + ioe));
        }
    }



    /**
     * Replacement for Integer.parseInt allowing "supercharged" non-decimal
     * constants. In contrast to Integer.parseInt, works for 0x80000000 and
     * higher octal and hex constants as well as -MIN_VALUE which is allowed in
     * case that the minus sign has been interpreted as an unary minus. The
     * method will return Integer.MIN_VALUE in that case; this is fine as
     * -MIN_VALUE == MIN_VALUE.
     */
    public static int parseInt(String nm) throws NumberFormatException {
        int radix;
        boolean negative = false;
        int result;

        int index = 0;
        if (nm.startsWith("-")) {
            negative = true;
            index++;
        }
        if (nm.startsWith("0x", index) || nm.startsWith("0X", index)) {
            index += 2;
            radix = 16;
        } else if (nm.startsWith("0", index) && nm.length() > 1 + index) {
            index++;
            radix = 8;
        } else {
            radix = 10;
        }
        if (nm.startsWith("-", index))
            throw new NumberFormatException("Negative sign in wrong position");
        int len = nm.length() - index;
        if (radix == 16 && len == 8) {
            char first = nm.charAt(index);
            index += 1;
            result = Integer.valueOf(nm.substring(index), radix).intValue();
            result |= Character.digit(first, 16) << 28;
            return negative ? -result : result;
        }
        if (radix == 8 && len == 11) {
            char first = nm.charAt(index);
            index += 1;
            result = Integer.valueOf(nm.substring(index), radix).intValue();
            result |= Character.digit(first, 8) << 30;
            return negative ? -result : result;
        }
        if (!negative && radix == 10 && len == 10 && nm.indexOf("2147483648", index) == index) {
            return Integer.MIN_VALUE;
        }
        result = Integer.valueOf(nm.substring(index), radix).intValue();
        return negative ? -result : result;
    }

    /**
     * Replacement for Long.parseLong which is not available in JDK 1.1 and does
     * not handle 'l' or 'L' suffices in JDK 1.2.
     */
    public static long parseLong(String nm) throws NumberFormatException {
    	// fixes a bug
    	if (nm.equalsIgnoreCase("0L"))
    		return 0;
    	
        int radix;
        boolean negative = false;
        long result;

        int index = 0;
        if (nm.startsWith("-")) {
            negative = true;
            index++;
        }
        if (nm.startsWith("0x", index) || nm.startsWith("0X", index)) {
            index += 2;
            radix = 16;
        } else if (nm.startsWith("0", index) && nm.length() > 1 + index) {
            index++;
            radix = 8;
        } else {
            radix = 10;
        }

        if (nm.startsWith("-", index))
            throw new NumberFormatException("Negative sign in wrong position");
        int endIndex = nm.length();
        if (nm.endsWith("L") || nm.endsWith("l")) {
            endIndex -= 1;
        }

        int len = endIndex - index;
        if (radix == 16 && len == 16) {
            char first = nm.charAt(index);
            index += 1;
            result = Long.valueOf(nm.substring(index, endIndex), radix).longValue();
            result |= (long) Character.digit(first, 16) << 60;
            return negative ? -result : result;
        }
        if (radix == 8 && len == 21) {
            char first = nm.charAt(index);
            index += 1;
            result = Long.valueOf(nm.substring(index, endIndex), radix).longValue();
            result |= Character.digit(first, 8) << 63;
            return negative ? -result : result;
        }
        if (!negative && radix == 10 && len == 19 && nm.indexOf("9223372036854775808", index) == index) {
            return Long.MIN_VALUE;
        }
        result = Long.valueOf(nm.substring(index, endIndex), radix).longValue();
        return negative ? -result : result;
    }

    /**
     * Creates a syntactical representation of the source element.
     */
    String toSource(JavaSourceElement jse) {
        synchronized (writer) {
            sourcePrinter.setIndentationLevel(0);
            jse.accept(sourcePrinter);
            StringBuffer buf = writer.getBuffer();
            String str = buf.toString();
            buf.setLength(0);
            return str;
        }
    }

    /**
     * Returns a new suitable {@link recoder.java.PrettyPrinter}obeying the
     * current project settings for the specified writer,
     * 
     * @param out
     *            the (initial) writer to print to.
     * @return a new pretty printer.
     */
    public PrettyPrinter getPrettyPrinter(Writer out) {
        return new PrettyPrinter(out, serviceConfiguration.getProjectSettings().getProperties());
    }

    public void propertyChange(PropertyChangeEvent evt) {
        sourcePrinter = new PrettyPrinter(writer, serviceConfiguration.getProjectSettings().getProperties());
        String changedProp = evt.getPropertyName();
        if (changedProp.equals(PropertyNames.JDK1_4)) {
            parser.setAwareOfAssert(StringUtils.parseBooleanProperty(evt.getNewValue().toString()));
            // call automatically sets Java_5 to false if neccessary.
        }
        if (changedProp.equals(PropertyNames.JAVA_5)) {
            parser.setJava5(StringUtils.parseBooleanProperty(evt.getNewValue().toString()));
            // call automatically sets awareOfAssert to true if neccessary.
        }
        if (changedProp.equals(PropertyNames.ADD_NEWLINE_AT_END_OF_FILE)) {
        	useAddNewlineReader = StringUtils.parseBooleanProperty(evt.getNewValue().toString());
        }
    }

    /**
     * Demo program reading a single source file and writing it back to stdout
     * using the default {@link PrettyPrinter}.
     */
    public static void main(String[] args) throws Exception {
    	if (args.length < 1) {
            System.err.println("Requires a java source file as argument");
            System.exit(1);
        }
        try {
            CompilationUnit cu = new DefaultServiceConfiguration().getProgramFactory().parseCompilationUnit(
                    new FileReader(args[0]));
            System.out.println(cu.toSource());
        } catch (IOException ioe) {
            System.err.println(ioe);
            ioe.printStackTrace();
        } catch (ParserException pe) {
            System.err.println(pe);
            pe.printStackTrace();
        }
    }

    /**
     * Creates a new {@link Comment}.
     * 
     * @return a new instance of Comment.
     */
    public Comment createComment() {
        return new Comment();
    }

    /**
     * Creates a new {@link Comment}.
     * 
     * @return a new instance of Comment.
     */
    public Comment createComment(String text) {
        return new Comment(text);
    }

    /**
     * Creates a new {@link Comment}.
     * 
     * @return a new instance of Comment.
     */
    public Comment createComment(String text, boolean prefixed) {
        return new Comment(text, prefixed);
    }

    /**
     * Creates a new {@link CompilationUnit}.
     * 
     * @return a new instance of CompilationUnit.
     */
    public CompilationUnit createCompilationUnit() {
        return new CompilationUnit();
    }

    /**
     * Creates a new {@link CompilationUnit}.
     * 
     * @return a new instance of CompilationUnit.
     */
    public CompilationUnit createCompilationUnit(PackageSpecification pkg, ASTList<Import> imports,
    		ASTList<TypeDeclaration> typeDeclarations) {
        return new CompilationUnit(pkg, imports, typeDeclarations);
    }

    /**
     * Creates a new {@link DocComment}.
     * 
     * @return a new instance of DocComment.
     */
    public DocComment createDocComment() {
        return new DocComment();
    }

    /**
     * Creates a new {@link DocComment}.
     * 
     * @return a new instance of DocComment.
     */
    public DocComment createDocComment(String text) {
        return new DocComment(text);
    }

    /**
     * Creates a new {@link Identifier}.
     * 
     * @return a new instance of Identifier.
     */
    public Identifier createIdentifier() {
        Identifier res = new Identifier();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Identifier}.
     * 
     * @return a new instance of Identifier.
     */
    public Identifier createIdentifier(String text) {
        Identifier res = new Identifier(text);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Import}.
     * 
     * @return a new instance of Import.
     */
    public Import createImport() {
        Import res = new Import();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Import}.
     * 
     * @return a new instance of Import.
     */
    public Import createImport(TypeReference t, boolean multi) {
        Import res = new Import(t, multi);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Import}.
     * 
     * @return a new instance of Import.
     */
    public Import createImport(PackageReference t) {
        Import res = new Import(t);
        trace(res);
        return res;
    }
    
    public Import createStaticImport(TypeReference t) {
        Import res = new Import(t, true, true);
        trace(res);
        return res;
    }
    
    public Import createStaticImport(TypeReference t, Identifier id) {
        Import res = new Import(t, id);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PackageSpecification}.
     * 
     * @return a new instance of PackageSpecification.
     */
    public PackageSpecification createPackageSpecification() {
        PackageSpecification res =  new PackageSpecification();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PackageSpecification}.
     * 
     * @return a new instance of PackageSpecification.
     */
    public PackageSpecification createPackageSpecification(PackageReference pkg) {
        PackageSpecification res =  new PackageSpecification(pkg);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link SingleLineComment}.
     * 
     * @return a new instance of SingleLineComment.
     */
    public SingleLineComment createSingleLineComment() {
        return new SingleLineComment();
    }

    /**
     * Creates a new {@link SingleLineComment}.
     * 
     * @return a new instance of SingleLineComment.
     */
    public SingleLineComment createSingleLineComment(String text) {
        return new SingleLineComment(text);
    }

    /**
     * Creates a new {@link TypeReference}.
     * 
     * @return a new instance of TypeReference.
     */
    public TypeReference createTypeReference() {
        TypeReference res = new TypeReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link TypeReference}.
     * 
     * @return a new instance of TypeReference.
     */
    public TypeReference createTypeReference(Identifier name) {
        TypeReference res = new TypeReference(name);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link TypeReference}.
     * 
     * @return a new instance of TypeReference.
     */
    public TypeReference createTypeReference(ReferencePrefix prefix, Identifier name) {
        TypeReference res =  new TypeReference(prefix, name);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link TypeReference}.
     * 
     * @return a new instance of TypeReference.
     */
    public TypeReference createTypeReference(Identifier name, int dim) {
        TypeReference res = new TypeReference(name, dim);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PackageReference}.
     * 
     * @return a new instance of PackageReference.
     */
    public PackageReference createPackageReference() {
        PackageReference res = new PackageReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PackageReference}.
     * 
     * @return a new instance of PackageReference.
     */
    public PackageReference createPackageReference(Identifier id) {
        PackageReference res = new PackageReference(id);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PackageReference}.
     * 
     * @return a new instance of PackageReference.
     */
    public PackageReference createPackageReference(PackageReference path, Identifier id) {
        PackageReference res = new PackageReference(path, id);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link UncollatedReferenceQualifier}.
     * 
     * @return a new instance of UncollatedReferenceQualifier.
     */
    public UncollatedReferenceQualifier createUncollatedReferenceQualifier() {
        return new UncollatedReferenceQualifier();
    }

    /**
     * Creates a new {@link UncollatedReferenceQualifier}.
     * 
     * @return a new instance of UncollatedReferenceQualifier.
     */
    public UncollatedReferenceQualifier createUncollatedReferenceQualifier(Identifier id) {
        return new UncollatedReferenceQualifier(id);
    }

    /**
     * Creates a new {@link UncollatedReferenceQualifier}.
     * 
     * @return a new instance of UncollatedReferenceQualifier.
     */
    public UncollatedReferenceQualifier createUncollatedReferenceQualifier(ReferencePrefix prefix, Identifier id) {
        return new UncollatedReferenceQualifier(prefix, id);
    }

    /**
     * Creates a new {@link ClassDeclaration}.
     * 
     * @return a new instance of ClassDeclaration.
     */
    public ClassDeclaration createClassDeclaration() {
        ClassDeclaration res = new ClassDeclaration();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ClassDeclaration}.
     * 
     * @return a new instance of ClassDeclaration.
     */
    public ClassDeclaration createClassDeclaration(ASTList<DeclarationSpecifier> declSpecs, Identifier name, Extends extended,
            Implements implemented, ASTList<MemberDeclaration> members) {
        ClassDeclaration res = new ClassDeclaration(declSpecs, name, extended, implemented, members);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ClassDeclaration}.
     * 
     * @return a new instance of ClassDeclaration.
     */
    public ClassDeclaration createClassDeclaration(ASTList<MemberDeclaration> members) {
        ClassDeclaration res = new ClassDeclaration(members);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ClassInitializer}.
     * 
     * @return a new instance of ClassInitializer.
     */
    public ClassInitializer createClassInitializer() {
        ClassInitializer res = new ClassInitializer();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ClassInitializer}.
     * 
     * @return a new instance of ClassInitializer.
     */
    public ClassInitializer createClassInitializer(StatementBlock body) {
        ClassInitializer res = new ClassInitializer(body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ClassInitializer}.
     * 
     * @return a new instance of ClassInitializer.
     */
    public ClassInitializer createClassInitializer(Static modifier, StatementBlock body) {
        ClassInitializer res =new ClassInitializer(modifier, body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ConstructorDeclaration}.
     * 
     * @return a new instance of ConstructorDeclaration.
     */
    public ConstructorDeclaration createConstructorDeclaration() {
    	ConstructorDeclaration res = new ConstructorDeclaration();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ConstructorDeclaration}.
     * 
     * @return a new instance of ConstructorDeclaration.
     */
    public ConstructorDeclaration createConstructorDeclaration(VisibilityModifier modifier, Identifier name,
    		ASTList<ParameterDeclaration> parameters, Throws exceptions, StatementBlock body) {
        ConstructorDeclaration res = new ConstructorDeclaration(modifier, name, parameters, exceptions, body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Throws}.
     * 
     * @return a new instance of Throws.
     */
    public Throws createThrows() {
       Throws res = new Throws();
       trace(res);
       return res;
    }

    /**
     * Creates a new {@link Throws}.
     * 
     * @return a new instance of Throws.
     */
    public Throws createThrows(TypeReference exception) {
        Throws res = new Throws(exception);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Throws}.
     * 
     * @return a new instance of Throws.
     */
    public Throws createThrows(ASTList<TypeReference> list) {
        Throws res = new Throws(list);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldDeclaration}.
     * 
     * @return a new instance of FieldDeclaration.
     */
    public FieldDeclaration createFieldDeclaration() {
        FieldDeclaration res = new FieldDeclaration();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldDeclaration}.
     * 
     * @return a new instance of FieldDeclaration.
     */
    public FieldDeclaration createFieldDeclaration(TypeReference typeRef, Identifier name) {
        FieldDeclaration res = new FieldDeclaration(typeRef, name);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldDeclaration}.
     * 
     * @return a new instance of FieldDeclaration.
     */
    public FieldDeclaration createFieldDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, Identifier name,
            Expression init) {
        FieldDeclaration res = new FieldDeclaration(mods, typeRef, name, init);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldDeclaration}.
     * 
     * @return a new instance of FieldDeclaration.
     */
    public FieldDeclaration createFieldDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef,
    		ASTList<FieldSpecification> vars) {
        FieldDeclaration res = new FieldDeclaration(mods, typeRef, vars);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Extends}.
     * 
     * @return a new instance of Extends.
     */
    public Extends createExtends() {
        Extends res = new Extends();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Extends}.
     * 
     * @return a new instance of Extends.
     */
    public Extends createExtends(TypeReference supertype) {
        Extends res = new Extends(supertype);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Extends}.
     * 
     * @return a new instance of Extends.
     */
    public Extends createExtends(ASTList<TypeReference> list) {
        Extends res = new Extends(list);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Implements}.
     * 
     * @return a new instance of Implements.
     */
    public Implements createImplements() {
        Implements res = new Implements();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Implements}.
     * 
     * @return a new instance of Implements.
     */
    public Implements createImplements(TypeReference supertype) {
        Implements res = new Implements(supertype);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Implements}.
     * 
     * @return a new instance of Implements.
     */
    public Implements createImplements(ASTList<TypeReference> list) {
        Implements res = new Implements(list);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link InterfaceDeclaration}.
     * 
     * @return a new instance of InterfaceDeclaration.
     */
    public InterfaceDeclaration createInterfaceDeclaration() {
        InterfaceDeclaration res = new InterfaceDeclaration();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link InterfaceDeclaration}.
     * 
     * @return a new instance of InterfaceDeclaration.
     */
    public InterfaceDeclaration createInterfaceDeclaration(ASTList<DeclarationSpecifier> modifiers, Identifier name,
            Extends extended, ASTList<MemberDeclaration> members) {
        InterfaceDeclaration res = new InterfaceDeclaration(modifiers, name, extended, members);
        trace(res);
        return res;
    }
    
    public AnnotationDeclaration createAnnotationDeclaration() {
        AnnotationDeclaration res = new AnnotationDeclaration();
        trace(res);
        return res;
    }
    
    public AnnotationDeclaration createAnnotationDeclaration(ASTList<DeclarationSpecifier> modifiers, Identifier name,
    		ASTList<MemberDeclaration> members) {
        AnnotationDeclaration res = new AnnotationDeclaration(modifiers, name, members);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     * 
     * @return a new instance of LocalVariableDeclaration.
     */
    public LocalVariableDeclaration createLocalVariableDeclaration() {
        LocalVariableDeclaration res = new LocalVariableDeclaration();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     * 
     * @return a new instance of LocalVariableDeclaration.
     */
    public LocalVariableDeclaration createLocalVariableDeclaration(TypeReference typeRef, Identifier name) {
        LocalVariableDeclaration res = new LocalVariableDeclaration(typeRef, name);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     * 
     * @return a new instance of LocalVariableDeclaration.
     */
    public LocalVariableDeclaration createLocalVariableDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef,
    		ASTList<VariableSpecification> vars) {
        LocalVariableDeclaration res = new LocalVariableDeclaration(mods, typeRef, vars);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     * 
     * @return a new instance of LocalVariableDeclaration.
     */
    public LocalVariableDeclaration createLocalVariableDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef,
            Identifier name, Expression init) {
        LocalVariableDeclaration res = new LocalVariableDeclaration(mods, typeRef, name, init);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MethodDeclaration}.
     * 
     * @return a new instance of MethodDeclaration.
     */
    public MethodDeclaration createMethodDeclaration() {
        MethodDeclaration res = new MethodDeclaration();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MethodDeclaration}.
     * 
     * @return a new instance of MethodDeclaration.
     */
    public MethodDeclaration createMethodDeclaration(ASTList<DeclarationSpecifier> modifiers, TypeReference returnType,
            Identifier name, ASTList<ParameterDeclaration> parameters, Throws exceptions) {
        MethodDeclaration res = new MethodDeclaration(modifiers, returnType, name, parameters, exceptions);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MethodDeclaration}.
     * 
     * @return a new instance of MethodDeclaration.
     */
    public MethodDeclaration createMethodDeclaration(ASTList<DeclarationSpecifier> modifiers, TypeReference returnType,
            Identifier name, ASTList<ParameterDeclaration> parameters, Throws exceptions, StatementBlock body) {
        MethodDeclaration res = new MethodDeclaration(modifiers, returnType, name, parameters, exceptions, body);
        trace(res);
        return res;
    }
    
    public AnnotationPropertyDeclaration createAnnotationPropertyDeclaration(ASTList<DeclarationSpecifier> modifiers, TypeReference returnType,
            Identifier name, Expression defaultValue) {
        AnnotationPropertyDeclaration res = new AnnotationPropertyDeclaration(modifiers, returnType, name, defaultValue);
        trace(res);
        return res;
    }
    
    /**
     * Creates a new {@link ParameterDeclaration}.
     * 
     * @return a new instance of ParameterDeclaration.
     */
    public ParameterDeclaration createParameterDeclaration() {
        ParameterDeclaration res = new ParameterDeclaration();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ParameterDeclaration}.
     * 
     * @return a new instance of ParameterDeclaration.
     */
    public ParameterDeclaration createParameterDeclaration(TypeReference typeRef, Identifier name) {
        ParameterDeclaration res = new ParameterDeclaration(typeRef, name);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ParameterDeclaration}.
     * 
     * @return a new instance of ParameterDeclaration.
     */
    public ParameterDeclaration createParameterDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef,
            Identifier name) {
        ParameterDeclaration res = new ParameterDeclaration(mods, typeRef, name);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link VariableSpecification}.
     * 
     * @return a new instance of VariableSpecification.
     */
    public VariableSpecification createVariableSpecification() {
        VariableSpecification res =  new VariableSpecification();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link VariableSpecification}.
     * 
     * @return a new instance of VariableSpecification.
     */
    public VariableSpecification createVariableSpecification(Identifier name) {
        VariableSpecification res = new VariableSpecification(name);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link VariableSpecification}.
     * 
     * @return a new instance of VariableSpecification.
     */
    public VariableSpecification createVariableSpecification(Identifier name, Expression init) {
        VariableSpecification res = new VariableSpecification(name, init);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link VariableSpecification}.
     * 
     * @return a new instance of VariableSpecification.
     */
    public VariableSpecification createVariableSpecification(Identifier name, int dimensions, Expression init) {
        VariableSpecification res =  new VariableSpecification(name, dimensions, init);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldSpecification}.
     * 
     * @return a new instance of FieldSpecification.
     */
    public FieldSpecification createFieldSpecification() {
        FieldSpecification res = new FieldSpecification();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldSpecification}.
     * 
     * @return a new instance of FieldSpecification.
     */
    public FieldSpecification createFieldSpecification(Identifier name) {
        FieldSpecification res =  new FieldSpecification(name);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldSpecification}.
     * 
     * @return a new instance of FieldSpecification.
     */
    public FieldSpecification createFieldSpecification(Identifier name, Expression init) {
        FieldSpecification res =  new FieldSpecification(name, init);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldSpecification}.
     * 
     * @return a new instance of FieldSpecification.
     */
    public FieldSpecification createFieldSpecification(Identifier name, int dimensions, Expression init) {
        FieldSpecification res = new FieldSpecification(name, dimensions, init);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ArrayInitializer}.
     * 
     * @return a new instance of ArrayInitializer.
     */
    public ArrayInitializer createArrayInitializer() {
        ArrayInitializer res =  new ArrayInitializer();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ArrayInitializer}.
     * 
     * @return a new instance of ArrayInitializer.
     */
    public ArrayInitializer createArrayInitializer(ASTList<Expression> args) {
        ArrayInitializer res =  new ArrayInitializer(args);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ParenthesizedExpression}.
     * 
     * @return a new instance of ParenthesizedExpression.
     */
    public ParenthesizedExpression createParenthesizedExpression() {
        ParenthesizedExpression res = new ParenthesizedExpression();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ParenthesizedExpression}.
     * 
     * @return a new instance of ParenthesizedExpression.
     */
    public ParenthesizedExpression createParenthesizedExpression(Expression child) {
    	ParenthesizedExpression res = new ParenthesizedExpression(child);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BooleanLiteral}.
     * 
     * @return a new instance of BooleanLiteral.
     */
    public BooleanLiteral createBooleanLiteral() {
        BooleanLiteral res = new BooleanLiteral();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BooleanLiteral}.
     * 
     * @return a new instance of BooleanLiteral.
     */
    public BooleanLiteral createBooleanLiteral(boolean value) {
        BooleanLiteral res = new BooleanLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link CharLiteral}.
     * 
     * @return a new instance of CharLiteral.
     */
    public CharLiteral createCharLiteral() {
        CharLiteral res = new CharLiteral();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link CharLiteral}.
     * 
     * @return a new instance of CharLiteral.
     */
    public CharLiteral createCharLiteral(char value) {
        CharLiteral res = new CharLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link CharLiteral}.
     * 
     * @return a new instance of CharLiteral.
     */
    public CharLiteral createCharLiteral(String value) {
        CharLiteral res = new CharLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link DoubleLiteral}.
     * 
     * @return a new instance of DoubleLiteral.
     */
    public DoubleLiteral createDoubleLiteral() {
        DoubleLiteral res = new DoubleLiteral();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link DoubleLiteral}.
     * 
     * @return a new instance of DoubleLiteral.
     */
    public DoubleLiteral createDoubleLiteral(double value) {
        DoubleLiteral res = new DoubleLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link DoubleLiteral}.
     * 
     * @return a new instance of DoubleLiteral.
     */
    public DoubleLiteral createDoubleLiteral(String value) {
        DoubleLiteral res = new DoubleLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FloatLiteral}.
     * 
     * @return a new instance of FloatLiteral.
     */
    public FloatLiteral createFloatLiteral() {
        FloatLiteral res = new FloatLiteral();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FloatLiteral}.
     * 
     * @return a new instance of FloatLiteral.
     */
    public FloatLiteral createFloatLiteral(float value) {
        FloatLiteral res = new FloatLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FloatLiteral}.
     * 
     * @return a new instance of FloatLiteral.
     */
    public FloatLiteral createFloatLiteral(String value) {
        FloatLiteral res = new FloatLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link IntLiteral}.
     * 
     * @return a new instance of IntLiteral.
     */
    public IntLiteral createIntLiteral() {
        IntLiteral res = new IntLiteral();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link IntLiteral}.
     * 
     * @return a new instance of IntLiteral.
     */
    public IntLiteral createIntLiteral(int value) {
        IntLiteral res = new IntLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link IntLiteral}.
     * 
     * @return a new instance of IntLiteral.
     */
    public IntLiteral createIntLiteral(String value) {
        IntLiteral res = new IntLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LongLiteral}.
     * 
     * @return a new instance of LongLiteral.
     */
    public LongLiteral createLongLiteral() {
        LongLiteral res = new LongLiteral();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LongLiteral}.
     * 
     * @return a new instance of LongLiteral.
     */
    public LongLiteral createLongLiteral(long value) {
        LongLiteral res = new LongLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LongLiteral}.
     * 
     * @return a new instance of LongLiteral.
     */
    public LongLiteral createLongLiteral(String value) {
        LongLiteral res = new LongLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link NullLiteral}.
     * 
     * @return a new instance of NullLiteral.
     */
    public NullLiteral createNullLiteral() {
        NullLiteral res =  new NullLiteral();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link StringLiteral}.
     * 
     * @return a new instance of StringLiteral.
     */
    public StringLiteral createStringLiteral() {
        StringLiteral res = new StringLiteral();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link StringLiteral}.
     * 
     * @return a new instance of StringLiteral.
     */
    public StringLiteral createStringLiteral(String value) {
        StringLiteral res = new StringLiteral(value);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ArrayReference}.
     * 
     * @return a new instance of ArrayReference.
     */
    public ArrayReference createArrayReference() {
        ArrayReference res = new ArrayReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ArrayReference}.
     * 
     * @return a new instance of ArrayReference.
     */
    public ArrayReference createArrayReference(ReferencePrefix accessPath, ASTList<Expression> initializers) {
        ArrayReference res = new ArrayReference(accessPath, initializers);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldReference}.
     * 
     * @return a new instance of FieldReference.
     */
    public FieldReference createFieldReference() {
        FieldReference res = new FieldReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldReference}.
     * 
     * @return a new instance of FieldReference.
     */
    public FieldReference createFieldReference(Identifier id) {
        FieldReference res = new FieldReference(id);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link FieldReference}.
     * 
     * @return a new instance of FieldReference.
     */
    public FieldReference createFieldReference(ReferencePrefix prefix, Identifier id) {
        FieldReference res = new FieldReference(prefix, id);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MetaClassReference}.
     * 
     * @return a new instance of MetaClassReference.
     */
    public MetaClassReference createMetaClassReference() {
        MetaClassReference res = new MetaClassReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MetaClassReference}.
     * 
     * @return a new instance of MetaClassReference.
     */
    public MetaClassReference createMetaClassReference(TypeReference reference) {
        MetaClassReference res = new MetaClassReference(reference);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MethodReference}.
     * 
     * @return a new instance of MethodReference.
     */
    public MethodReference createMethodReference() {
        MethodReference res = new MethodReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MethodReference}.
     * 
     * @return a new instance of MethodReference.
     */
    public MethodReference createMethodReference(Identifier name) {
        MethodReference res = new MethodReference(name);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MethodReference}.
     * 
     * @return a new instance of MethodReference.
     */
    public MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name) {
        MethodReference res = new MethodReference(accessPath, name);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MethodReference}.
     * 
     * @return a new instance of MethodReference.
     */
    public MethodReference createMethodReference(Identifier name, ASTList<Expression> args) {
        MethodReference res =new MethodReference(name, args);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MethodReference}.
     * 
     * @return a new instance of MethodReference.
     */
    public MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name, ASTList<Expression> args) {
        MethodReference res = new MethodReference(accessPath, name, args);
        trace(res);
        return res;
    }
    
    public MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name, ASTList<Expression> args,
    											 ASTList<TypeArgumentDeclaration> typeArgs) {
        MethodReference res = new MethodReference(accessPath, name, args, typeArgs);
        trace(res);
        return res;
    }
    
    public AnnotationPropertyReference createAnnotationPropertyReference(String id) {
    	Identifier ident = createIdentifier(id);
    	AnnotationPropertyReference res = new AnnotationPropertyReference(ident);
        trace(res);
        return res;
    }

    public AnnotationPropertyReference createAnnotationPropertyReference(Identifier id) {
    	AnnotationPropertyReference res = new AnnotationPropertyReference(id);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link SuperConstructorReference}.
     * 
     * @return a new instance of SuperConstructorReference.
     */
    public SuperConstructorReference createSuperConstructorReference() {
        SuperConstructorReference res = new SuperConstructorReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link SuperConstructorReference}.
     * 
     * @return a new instance of SuperConstructorReference.
     */
    public SuperConstructorReference createSuperConstructorReference(ASTList<Expression> arguments) {
        SuperConstructorReference res = new SuperConstructorReference(arguments);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link SuperConstructorReference}.
     * 
     * @return a new instance of SuperConstructorReference.
     */
    public SuperConstructorReference createSuperConstructorReference(ReferencePrefix path,
    		ASTList<Expression> arguments) {
        SuperConstructorReference res = new SuperConstructorReference(path, arguments);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link SuperReference}.
     * 
     * @return a new instance of SuperReference.
     */
    public SuperReference createSuperReference() {
        SuperReference res = new SuperReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link SuperReference}.
     * 
     * @return a new instance of SuperReference.
     */
    public SuperReference createSuperReference(ReferencePrefix accessPath) {
        SuperReference res = new SuperReference(accessPath);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ThisConstructorReference}.
     * 
     * @return a new instance of ThisConstructorReference.
     */
    public ThisConstructorReference createThisConstructorReference() {
        ThisConstructorReference res = new ThisConstructorReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ThisConstructorReference}.
     * 
     * @return a new instance of ThisConstructorReference.
     */
    public ThisConstructorReference createThisConstructorReference(ASTList<Expression> arguments) {
        ThisConstructorReference res = new ThisConstructorReference(arguments);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ThisReference}.
     * 
     * @return a new instance of ThisReference.
     */
    public ThisReference createThisReference() {
        ThisReference res = new ThisReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ThisReference}.
     * 
     * @return a new instance of ThisReference.
     */
    public ThisReference createThisReference(TypeReference outer) {
        ThisReference res = new ThisReference(outer);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link VariableReference}.
     * 
     * @return a new instance of VariableReference.
     */
    public VariableReference createVariableReference() {
        VariableReference res = new VariableReference();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link VariableReference}.
     * 
     * @return a new instance of VariableReference.
     */
    public VariableReference createVariableReference(Identifier id) {
        VariableReference res = new VariableReference(id);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryAnd}.
     * 
     * @return a new instance of BinaryAnd.
     */
    public BinaryAnd createBinaryAnd() {
        BinaryAnd res = new BinaryAnd();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryAnd}.
     * 
     * @return a new instance of BinaryAnd.
     */
    public BinaryAnd createBinaryAnd(Expression lhs, Expression rhs) {
        BinaryAnd res = new BinaryAnd(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryAndAssignment}.
     * 
     * @return a new instance of BinaryAndAssignment.
     */
    public BinaryAndAssignment createBinaryAndAssignment() {
        BinaryAndAssignment res = new BinaryAndAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryAndAssignment}.
     * 
     * @return a new instance of BinaryAndAssignment.
     */
    public BinaryAndAssignment createBinaryAndAssignment(Expression lhs, Expression rhs) {
        BinaryAndAssignment res = new BinaryAndAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryNot}.
     * 
     * @return a new instance of BinaryNot.
     */
    public BinaryNot createBinaryNot() {
        BinaryNot res = new BinaryNot();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryNot}.
     * 
     * @return a new instance of BinaryNot.
     */
    public BinaryNot createBinaryNot(Expression child) {
        BinaryNot res = new BinaryNot(child);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryOr}.
     * 
     * @return a new instance of BinaryOr.
     */
    public BinaryOr createBinaryOr() {
        BinaryOr res = new BinaryOr();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryOr}.
     * 
     * @return a new instance of BinaryOr.
     */
    public BinaryOr createBinaryOr(Expression lhs, Expression rhs) {
        BinaryOr res = new BinaryOr(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryOrAssignment}.
     * 
     * @return a new instance of BinaryOrAssignment.
     */
    public BinaryOrAssignment createBinaryOrAssignment() {
        BinaryOrAssignment res = new BinaryOrAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryOrAssignment}.
     * 
     * @return a new instance of BinaryOrAssignment.
     */
    public BinaryOrAssignment createBinaryOrAssignment(Expression lhs, Expression rhs) {
        BinaryOrAssignment res = new BinaryOrAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryXOr}.
     * 
     * @return a new instance of BinaryXOr.
     */
    public BinaryXOr createBinaryXOr() {
        BinaryXOr res = new BinaryXOr();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryXOr}.
     * 
     * @return a new instance of BinaryXOr.
     */
    public BinaryXOr createBinaryXOr(Expression lhs, Expression rhs) {
        BinaryXOr res = new BinaryXOr(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryXOrAssignment}.
     * 
     * @return a new instance of BinaryXOrAssignment.
     */
    public BinaryXOrAssignment createBinaryXOrAssignment() {
        BinaryXOrAssignment res = new BinaryXOrAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link BinaryXOrAssignment}.
     * 
     * @return a new instance of BinaryXOrAssignment.
     */
    public BinaryXOrAssignment createBinaryXOrAssignment(Expression lhs, Expression rhs) {
        BinaryXOrAssignment res = new BinaryXOrAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Conditional}.
     * 
     * @return a new instance of Conditional.
     */
    public Conditional createConditional() {
        Conditional res = new Conditional();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Conditional}.
     * 
     * @return a new instance of Conditional.
     */
    public Conditional createConditional(Expression guard, Expression thenExpr, Expression elseExpr) {
        Conditional res = new Conditional(guard, thenExpr, elseExpr);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link CopyAssignment}.
     * 
     * @return a new instance of CopyAssignment.
     */
    public CopyAssignment createCopyAssignment() {
        CopyAssignment res = new CopyAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link CopyAssignment}.
     * 
     * @return a new instance of CopyAssignment.
     */
    public CopyAssignment createCopyAssignment(Expression lhs, Expression rhs) {
        CopyAssignment res = new CopyAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Divide}.
     * 
     * @return a new instance of Divide.
     */
    public Divide createDivide() {
        Divide res = new Divide();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Divide}.
     * 
     * @return a new instance of Divide.
     */
    public Divide createDivide(Expression lhs, Expression rhs) {
        Divide res = new Divide(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link DivideAssignment}.
     * 
     * @return a new instance of DivideAssignment.
     */
    public DivideAssignment createDivideAssignment() {
        DivideAssignment res = new DivideAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link DivideAssignment}.
     * 
     * @return a new instance of DivideAssignment.
     */
    public DivideAssignment createDivideAssignment(Expression lhs, Expression rhs) {
        DivideAssignment res = new DivideAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Equals}.
     * 
     * @return a new instance of Equals.
     */
    public Equals createEquals() {
        Equals res = new Equals();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Equals}.
     * 
     * @return a new instance of Equals.
     */
    public Equals createEquals(Expression lhs, Expression rhs) {
        Equals res = new Equals(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link GreaterOrEquals}.
     * 
     * @return a new instance of GreaterOrEquals.
     */
    public GreaterOrEquals createGreaterOrEquals() {
        GreaterOrEquals res = new GreaterOrEquals();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link GreaterOrEquals}.
     * 
     * @return a new instance of GreaterOrEquals.
     */
    public GreaterOrEquals createGreaterOrEquals(Expression lhs, Expression rhs) {
        GreaterOrEquals res = new GreaterOrEquals(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link GreaterThan}.
     * 
     * @return a new instance of GreaterThan.
     */
    public GreaterThan createGreaterThan() {
        GreaterThan res = new GreaterThan();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link GreaterThan}.
     * 
     * @return a new instance of GreaterThan.
     */
    public GreaterThan createGreaterThan(Expression lhs, Expression rhs) {
        GreaterThan res = new GreaterThan(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Instanceof}.
     * 
     * @return a new instance of Instanceof.
     */
    public Instanceof createInstanceof() {
        Instanceof res = new Instanceof();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Instanceof}.
     * 
     * @return a new instance of Instanceof.
     */
    public Instanceof createInstanceof(Expression child, TypeReference typeref) {
        Instanceof res = new Instanceof(child, typeref);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LessOrEquals}.
     * 
     * @return a new instance of LessOrEquals.
     */
    public LessOrEquals createLessOrEquals() {
        LessOrEquals res = new LessOrEquals();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LessOrEquals}.
     * 
     * @return a new instance of LessOrEquals.
     */
    public LessOrEquals createLessOrEquals(Expression lhs, Expression rhs) {
        LessOrEquals res = new LessOrEquals(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LessThan}.
     * 
     * @return a new instance of LessThan.
     */
    public LessThan createLessThan() {
        LessThan res = new LessThan();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LessThan}.
     * 
     * @return a new instance of LessThan.
     */
    public LessThan createLessThan(Expression lhs, Expression rhs) {
        LessThan res = new LessThan(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LogicalAnd}.
     * 
     * @return a new instance of LogicalAnd.
     */
    public LogicalAnd createLogicalAnd() {
        LogicalAnd res = new LogicalAnd();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LogicalAnd}.
     * 
     * @return a new instance of LogicalAnd.
     */
    public LogicalAnd createLogicalAnd(Expression lhs, Expression rhs) {
        LogicalAnd res = new LogicalAnd(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LogicalNot}.
     * 
     * @return a new instance of LogicalNot.
     */
    public LogicalNot createLogicalNot() {
        LogicalNot res = new LogicalNot();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LogicalNot}.
     * 
     * @return a new instance of LogicalNot.
     */
    public LogicalNot createLogicalNot(Expression child) {
        LogicalNot res = new LogicalNot(child);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LogicalOr}.
     * 
     * @return a new instance of LogicalOr.
     */
    public LogicalOr createLogicalOr() {
        LogicalOr res = new LogicalOr();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LogicalOr}.
     * 
     * @return a new instance of LogicalOr.
     */
    public LogicalOr createLogicalOr(Expression lhs, Expression rhs) {
        LogicalOr res = new LogicalOr(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Minus}.
     * 
     * @return a new instance of Minus.
     */
    public Minus createMinus() {
        Minus res = new Minus();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Minus}.
     * 
     * @return a new instance of Minus.
     */
    public Minus createMinus(Expression lhs, Expression rhs) {
        Minus res = new Minus(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MinusAssignment}.
     * 
     * @return a new instance of MinusAssignment.
     */
    public MinusAssignment createMinusAssignment() {
        MinusAssignment res = new MinusAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link MinusAssignment}.
     * 
     * @return a new instance of MinusAssignment.
     */
    public MinusAssignment createMinusAssignment(Expression lhs, Expression rhs) {
        MinusAssignment res = new MinusAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Modulo}.
     * 
     * @return a new instance of Modulo.
     */
    public Modulo createModulo() {
        Modulo res = new Modulo();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Modulo}.
     * 
     * @return a new instance of Modulo.
     */
    public Modulo createModulo(Expression lhs, Expression rhs) {
        Modulo res =new Modulo(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ModuloAssignment}.
     * 
     * @return a new instance of ModuloAssignment.
     */
    public ModuloAssignment createModuloAssignment() {
        ModuloAssignment res = new ModuloAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ModuloAssignment}.
     * 
     * @return a new instance of ModuloAssignment.
     */
    public ModuloAssignment createModuloAssignment(Expression lhs, Expression rhs) {
        ModuloAssignment res = new ModuloAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Negative}.
     * 
     * @return a new instance of Negative.
     */
    public Negative createNegative() {
        Negative res = new Negative();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Negative}.
     * 
     * @return a new instance of Negative.
     */
    public Negative createNegative(Expression child) {
        Negative res = new Negative(child);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link New}.
     * 
     * @return a new instance of New.
     */
    public New createNew() {
        New res = new New();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link New}.
     * 
     * @return a new instance of New.
     */
    public New createNew(ReferencePrefix accessPath, TypeReference constructorName, ASTList<Expression> arguments) {
        New res = new New(accessPath, constructorName, arguments);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link New}.
     * 
     * @return a new instance of New.
     */
    public New createNew(ReferencePrefix accessPath, TypeReference constructorName, ASTList<Expression> arguments,
            ClassDeclaration anonymousClass) {
        New res = new New(accessPath, constructorName, arguments, anonymousClass);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link NewArray}.
     * 
     * @return a new instance of NewArray.
     */
    public NewArray createNewArray() {
        NewArray res = new NewArray();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link NewArray}.
     * 
     * @return a new instance of NewArray.
     */
    public NewArray createNewArray(TypeReference arrayName, ASTList<Expression> dimExpr) {
        NewArray res = new NewArray(arrayName, dimExpr);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link NewArray}.
     * 
     * @return a new instance of NewArray.
     */
    public NewArray createNewArray(TypeReference arrayName, int dimensions, ArrayInitializer initializer) {
        NewArray res = new NewArray(arrayName, dimensions, initializer);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link NotEquals}.
     * 
     * @return a new instance of NotEquals.
     */
    public NotEquals createNotEquals() {
        NotEquals res = new NotEquals();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link NotEquals}.
     * 
     * @return a new instance of NotEquals.
     */
    public NotEquals createNotEquals(Expression lhs, Expression rhs) {
        NotEquals res = new NotEquals(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Plus}.
     * 
     * @return a new instance of Plus.
     */
    public Plus createPlus() {
        Plus res = new Plus();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Plus}.
     * 
     * @return a new instance of Plus.
     */
    public Plus createPlus(Expression lhs, Expression rhs) {
        Plus res =  new Plus(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PlusAssignment}.
     * 
     * @return a new instance of PlusAssignment.
     */
    public PlusAssignment createPlusAssignment() {
        PlusAssignment res = new PlusAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PlusAssignment}.
     * 
     * @return a new instance of PlusAssignment.
     */
    public PlusAssignment createPlusAssignment(Expression lhs, Expression rhs) {
        PlusAssignment res = new PlusAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Positive}.
     * 
     * @return a new instance of Positive.
     */
    public Positive createPositive() {
        Positive res = new Positive();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Positive}.
     * 
     * @return a new instance of Positive.
     */
    public Positive createPositive(Expression child) {
        Positive res = new Positive(child);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PostDecrement}.
     * 
     * @return a new instance of PostDecrement.
     */
    public PostDecrement createPostDecrement() {
        PostDecrement res = new PostDecrement();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PostDecrement}.
     * 
     * @return a new instance of PostDecrement.
     */
    public PostDecrement createPostDecrement(Expression child) {
        PostDecrement res = new PostDecrement(child);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PostIncrement}.
     * 
     * @return a new instance of PostIncrement.
     */
    public PostIncrement createPostIncrement() {
        PostIncrement res = new PostIncrement();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PostIncrement}.
     * 
     * @return a new instance of PostIncrement.
     */
    public PostIncrement createPostIncrement(Expression child) {
        PostIncrement res = new PostIncrement(child);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PreDecrement}.
     * 
     * @return a new instance of PreDecrement.
     */
    public PreDecrement createPreDecrement() {
        PreDecrement res = new PreDecrement();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PreDecrement}.
     * 
     * @return a new instance of PreDecrement.
     */
    public PreDecrement createPreDecrement(Expression child) {
        PreDecrement res = new PreDecrement(child);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PreIncrement}.
     * 
     * @return a new instance of PreIncrement.
     */
    public PreIncrement createPreIncrement() {
        PreIncrement res = new PreIncrement();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link PreIncrement}.
     * 
     * @return a new instance of PreIncrement.
     */
    public PreIncrement createPreIncrement(Expression child) {
        PreIncrement res = new PreIncrement(child);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ShiftLeft}.
     * 
     * @return a new instance of ShiftLeft.
     */
    public ShiftLeft createShiftLeft() {
        ShiftLeft res =  new ShiftLeft();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ShiftLeft}.
     * 
     * @return a new instance of ShiftLeft.
     */
    public ShiftLeft createShiftLeft(Expression lhs, Expression rhs) {
        ShiftLeft res = new ShiftLeft(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ShiftLeftAssignment}.
     * 
     * @return a new instance of ShiftLeftAssignment.
     */
    public ShiftLeftAssignment createShiftLeftAssignment() {
        ShiftLeftAssignment res = new ShiftLeftAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ShiftLeftAssignment}.
     * 
     * @return a new instance of ShiftLeftAssignment.
     */
    public ShiftLeftAssignment createShiftLeftAssignment(Expression lhs, Expression rhs) {
        ShiftLeftAssignment res = new ShiftLeftAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ShiftRight}.
     * 
     * @return a new instance of ShiftRight.
     */
    public ShiftRight createShiftRight() {
        ShiftRight res = new ShiftRight();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ShiftRight}.
     * 
     * @return a new instance of ShiftRight.
     */
    public ShiftRight createShiftRight(Expression lhs, Expression rhs) {
        ShiftRight res = new ShiftRight(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ShiftRightAssignment}.
     * 
     * @return a new instance of ShiftRightAssignment.
     */
    public ShiftRightAssignment createShiftRightAssignment() {
        ShiftRightAssignment res =  new ShiftRightAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link ShiftRightAssignment}.
     * 
     * @return a new instance of ShiftRightAssignment.
     */
    public ShiftRightAssignment createShiftRightAssignment(Expression lhs, Expression rhs) {
        ShiftRightAssignment res =  new ShiftRightAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Times}.
     * 
     * @return a new instance of Times.
     */
    public Times createTimes() {
        Times res =  new Times();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Times}.
     * 
     * @return a new instance of Times.
     */
    public Times createTimes(Expression lhs, Expression rhs) {
        Times res =  new Times(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link TimesAssignment}.
     * 
     * @return a new instance of TimesAssignment.
     */
    public TimesAssignment createTimesAssignment() {
        TimesAssignment res = new TimesAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link TimesAssignment}.
     * 
     * @return a new instance of TimesAssignment.
     */
    public TimesAssignment createTimesAssignment(Expression lhs, Expression rhs) {
        TimesAssignment res = new TimesAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link TypeCast}.
     * 
     * @return a new instance of TypeCast.
     */
    public TypeCast createTypeCast() {
        TypeCast res = new TypeCast();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link TypeCast}.
     * 
     * @return a new instance of TypeCast.
     */
    public TypeCast createTypeCast(Expression child, TypeReference typeref) {
        TypeCast res = new TypeCast(child, typeref);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link UnsignedShiftRight}.
     * 
     * @return a new instance of UnsignedShiftRight.
     */
    public UnsignedShiftRight createUnsignedShiftRight() {
        UnsignedShiftRight res = new UnsignedShiftRight();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link UnsignedShiftRight}.
     * 
     * @return a new instance of UnsignedShiftRight.
     */
    public UnsignedShiftRight createUnsignedShiftRight(Expression lhs, Expression rhs) {
        UnsignedShiftRight res = new UnsignedShiftRight(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link UnsignedShiftRightAssignment}.
     * 
     * @return a new instance of UnsignedShiftRightAssignment.
     */
    public UnsignedShiftRightAssignment createUnsignedShiftRightAssignment() {
        UnsignedShiftRightAssignment res = new UnsignedShiftRightAssignment();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link UnsignedShiftRightAssignment}.
     * 
     * @return a new instance of UnsignedShiftRightAssignment.
     */
    public UnsignedShiftRightAssignment createUnsignedShiftRightAssignment(Expression lhs, Expression rhs) {
        UnsignedShiftRightAssignment res = new UnsignedShiftRightAssignment(lhs, rhs);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Abstract}.
     * 
     * @return a new instance of Abstract.
     */
    public Abstract createAbstract() {
        Abstract res = new Abstract();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Final}.
     * 
     * @return a new instance of Final.
     */
    public Final createFinal() {
        Final res = new Final();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Native}.
     * 
     * @return a new instance of Native.
     */
    public Native createNative() {
        Native res = new Native();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Private}.
     * 
     * @return a new instance of Private.
     */
    public Private createPrivate() {
        Private res = new Private();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Protected}.
     * 
     * @return a new instance of Protected.
     */
    public Protected createProtected() {
        Protected res = new Protected();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Public}.
     * 
     * @return a new instance of Public.
     */
    public Public createPublic() {
        Public res = new Public();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Static}.
     * 
     * @return a new instance of Static.
     */
    public Static createStatic() {
        Static res = new Static();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Synchronized}.
     * 
     * @return a new instance of Synchronized.
     */
    public Synchronized createSynchronized() {
        Synchronized res = new Synchronized();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Transient}.
     * 
     * @return a new instance of Transient.
     */
    public Transient createTransient() {
        Transient res = new Transient();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link StrictFp}.
     * 
     * @return a new instance of StrictFp.
     */
    public StrictFp createStrictFp() {
        StrictFp res = new StrictFp();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Volatile}.
     * 
     * @return a new instance of Volatile.
     */
    public Volatile createVolatile() {
        Volatile res = new Volatile();
        trace(res);
        return res;
    }
    
    public AnnotationUseSpecification createAnnotationUseSpecification() {
        AnnotationUseSpecification res = new AnnotationUseSpecification();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Break}.
     * 
     * @return a new instance of Break.
     */
    public Break createBreak() {
        Break res = new Break();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Break}.
     * 
     * @return a new instance of Break.
     */
    public Break createBreak(Identifier label) {
        Break res = new Break(label);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Case}.
     * 
     * @return a new instance of Case.
     */
    public Case createCase() {
        Case res = new Case();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Case}.
     * 
     * @return a new instance of Case.
     */
    public Case createCase(Expression e) {
        Case res = new Case(e);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Case}.
     * 
     * @return a new instance of Case.
     */
    public Case createCase(Expression e, ASTList<Statement> body) {
        Case res = new Case(e, body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Catch}.
     * 
     * @return a new instance of Catch.
     */
    public Catch createCatch() {
        Catch res = new Catch();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Catch}.
     * 
     * @return a new instance of Catch.
     */
    public Catch createCatch(ParameterDeclaration e, StatementBlock body) {
        Catch res = new Catch(e, body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Continue}.
     * 
     * @return a new instance of Continue.
     */
    public Continue createContinue() {
        Continue res =  new Continue();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Continue}.
     * 
     * @return a new instance of Continue.
     */
    public Continue createContinue(Identifier label) {
        Continue res = new Continue(label);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Default}.
     * 
     * @return a new instance of Default.
     */
    public Default createDefault() {
        Default res = new Default();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Default}.
     * 
     * @return a new instance of Default.
     */
    public Default createDefault(ASTList<Statement> body) {
        Default res = new Default(body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Do}.
     * 
     * @return a new instance of Do.
     */
    public Do createDo() {
        Do res = new Do();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Do}.
     * 
     * @return a new instance of Do.
     */
    public Do createDo(Expression guard) {
        Do res = new Do(guard);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Do}.
     * 
     * @return a new instance of Do.
     */
    public Do createDo(Expression guard, Statement body) {
        Do res = new Do(guard, body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Else}.
     * 
     * @return a new instance of Else.
     */
    public Else createElse() {
        Else res =  new Else();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Else}.
     * 
     * @return a new instance of Else.
     */
    public Else createElse(Statement body) {
        Else res =  new Else(body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link EmptyStatement}.
     * 
     * @return a new instance of EmptyStatement.
     */
    public EmptyStatement createEmptyStatement() {
        EmptyStatement res = new EmptyStatement();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Finally}.
     * 
     * @return a new instance of Finally.
     */
    public Finally createFinally() {
        Finally res =  new Finally();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Finally}.
     * 
     * @return a new instance of Finally.
     */
    public Finally createFinally(StatementBlock body) {
        Finally res = new Finally(body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link For}.
     * 
     * @return a new instance of For.
     */
    public For createFor() {
        For res = new For();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link For}.
     * 
     * @return a new instance of For.
     */
    public For createFor(ASTList<LoopInitializer> inits, Expression guard, ASTList<Expression> updates,
            Statement body) {
        For res = new For(inits, guard, updates, body);
        trace(res);
        return res;
    }
    
    public EnhancedFor createEnhancedFor() {
        EnhancedFor res = new EnhancedFor();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Assert}.
     * 
     * @return a new instance of Assert.
     */
    public Assert createAssert() {
        Assert res = new Assert();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Assert}.
     * 
     * @return a new instance of Assert.
     */
    public Assert createAssert(Expression cond) {
        Assert res = new Assert(cond);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Assert}.
     * 
     * @return a new instance of Assert.
     */
    public Assert createAssert(Expression cond, Expression msg) {
        Assert res = new Assert(cond, msg);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link If}.
     * 
     * @return a new instance of If.
     */
    public If createIf() {
        If res = new If();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link If}.
     * 
     * @return a new instance of If.
     */
    public If createIf(Expression e, Statement thenStatement) {
        If res = new If(e, thenStatement);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link If}.
     * 
     * @return a new instance of If.
     */
    public If createIf(Expression e, Then thenBranch) {
        If res = new If(e, thenBranch);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link If}.
     * 
     * @return a new instance of If.
     */
    public If createIf(Expression e, Then thenBranch, Else elseBranch) {
        If res = new If(e, thenBranch, elseBranch);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link If}.
     * 
     * @return a new instance of If.
     */
    public If createIf(Expression e, Statement thenStatement, Statement elseStatement) {
        If res = new If(e, thenStatement, elseStatement);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LabeledStatement}.
     * 
     * @return a new instance of LabeledStatement.
     */
    public LabeledStatement createLabeledStatement() {
        LabeledStatement res = new LabeledStatement();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LabeledStatement}.
     * 
     * @return a new instance of LabeledStatement.
     */
    public LabeledStatement createLabeledStatement(Identifier id) {
        LabeledStatement res = new LabeledStatement(id);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link LabeledStatement}.
     * 
     * @return a new instance of LabeledStatement.
     */
    public LabeledStatement createLabeledStatement(Identifier id, Statement statement) {
        LabeledStatement res = new LabeledStatement(id, statement);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Return}.
     * 
     * @return a new instance of Return.
     */
    public Return createReturn() {
        Return res = new Return();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Return}.
     * 
     * @return a new instance of Return.
     */
    public Return createReturn(Expression expr) {
        Return res = new Return(expr);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link StatementBlock}.
     * 
     * @return a new instance of StatementBlock.
     */
    public StatementBlock createStatementBlock() {
        StatementBlock res = new StatementBlock();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link StatementBlock}.
     * 
     * @return a new instance of StatementBlock.
     */
    public StatementBlock createStatementBlock(ASTList<Statement> block) {
        StatementBlock res = new StatementBlock(block);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Switch}.
     * 
     * @return a new instance of Switch.
     */
    public Switch createSwitch() {
        Switch res = new Switch();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Switch}.
     * 
     * @return a new instance of Switch.
     */
    public Switch createSwitch(Expression e) {
        Switch res = new Switch(e);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Switch}.
     * 
     * @return a new instance of Switch.
     */
    public Switch createSwitch(Expression e, ASTList<Branch> branches) {
        Switch res = new Switch(e, branches);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link SynchronizedBlock}.
     * 
     * @return a new instance of SynchronizedBlock.
     */
    public SynchronizedBlock createSynchronizedBlock() {
        SynchronizedBlock res = new SynchronizedBlock();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link SynchronizedBlock}.
     * 
     * @return a new instance of SynchronizedBlock.
     */
    public SynchronizedBlock createSynchronizedBlock(StatementBlock body) {
        SynchronizedBlock res = new SynchronizedBlock(body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link SynchronizedBlock}.
     * 
     * @return a new instance of SynchronizedBlock.
     */
    public SynchronizedBlock createSynchronizedBlock(Expression e, StatementBlock body) {
        SynchronizedBlock res = new SynchronizedBlock(e, body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Then}.
     * 
     * @return a new instance of Then.
     */
    public Then createThen() {
        Then res = new Then();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Then}.
     * 
     * @return a new instance of Then.
     */
    public Then createThen(Statement body) {
        Then res = new Then(body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Throw}.
     * 
     * @return a new instance of Throw.
     */
    public Throw createThrow() {
        Throw res =  new Throw();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Throw}.
     * 
     * @return a new instance of Throw.
     */
    public Throw createThrow(Expression expr) {
        Throw res = new Throw(expr);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Try}.
     * 
     * @return a new instance of Try.
     */
    public Try createTry() {
        Try res = new Try();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Try}.
     * 
     * @return a new instance of Try.
     */
    public Try createTry(StatementBlock body) {
        Try res = new Try(body);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link Try}.
     * 
     * @return a new instance of Try.
     */
    public Try createTry(StatementBlock body, ASTList<Branch> branches) {
        Try res = new Try(body, branches);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link While}.
     * 
     * @return a new instance of While.
     */
    public While createWhile() {
        While res = new While();
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link While}.
     * 
     * @return a new instance of While.
     */
    public While createWhile(Expression guard) {
        While res = new While(guard);
        trace(res);
        return res;
    }

    /**
     * Creates a new {@link While}.
     * 
     * @return a new instance of While.
     */
    public While createWhile(Expression guard, Statement body) {
        While res = new While(guard, body);
        trace(res);
        return res;
    }
}
