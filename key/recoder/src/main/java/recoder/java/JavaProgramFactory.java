package recoder.java;

import recoder.DefaultServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.ServiceConfiguration;
import recoder.convenience.TreeWalker;
import recoder.io.ProjectSettings;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.*;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.parser.JavaCCParser;
import recoder.util.StringUtils;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.*;
import java.nio.CharBuffer;
import java.util.ArrayList;
import java.util.List;

public class JavaProgramFactory implements ProgramFactory, PropertyChangeListener {
    private static final SourceElement.Position ZERO_POSITION = new SourceElement.Position(0, 0);
    private static final JavaProgramFactory theFactory = new JavaProgramFactory();
    private static ServiceConfiguration serviceConfiguration;
    private static StringWriter writer = new StringWriter();
    private static PrettyPrinter sourcePrinter;
    private static boolean useAddNewlineReader = true;
    private static final JavaCCParser parser = new JavaCCParser(System.in);

    public static JavaProgramFactory getInstance() {
        return theFactory;
    }

    private static void attachComment(Comment c, ProgramElement pe) {
        ASTArrayList aSTArrayList;
        ProgramElement dest = pe;
        if (c.isPrefixed() && pe instanceof CompilationUnit && ((CompilationUnit) pe).getChildCount() > 0) {
            ProgramElement fc = ((CompilationUnit) pe).getChildAt(0);
            int distcu = c.getStartPosition().getLine();
            int distfc = fc.getStartPosition().getLine() - c.getEndPosition().getLine();
            if (c instanceof SingleLineComment)
                distcu--;
            if (distcu >= distfc)
                dest = fc;
        } else if (!c.isPrefixed()) {
            NonTerminalProgramElement ppe = dest.getASTParent();
            int i = 0;
            if (ppe != null)
                for (; ppe.getChildAt(i) != dest; i++) ;
            if (i == 0) {
                c.setPrefixed(true);
            } else {
                dest = ppe.getChildAt(i - 1);
                while (dest instanceof NonTerminalProgramElement) {
                    ppe = (NonTerminalProgramElement) dest;
                    i = ppe.getChildCount();
                    if (i == 0)
                        break;
                    dest = ppe.getChildAt(i - 1);
                }
                ppe = dest.getASTParent();
                boolean doChange = false;
                while (ppe != null && ppe.getASTParent() != null && ppe.getEndPosition().compareTo(dest.getEndPosition()) >= 0 && ppe.getASTParent().getEndPosition().compareTo(c.getStartPosition()) <= 0) {
                    ppe = ppe.getASTParent();
                    doChange = true;
                }
                if (ppe != null && doChange)
                    dest = ppe;
                if (dest instanceof NonTerminalProgramElement) {
                    ppe = (NonTerminalProgramElement) dest;
                    if (ppe.getEndPosition().compareTo(c.getStartPosition()) >= 0) {
                        while (ppe.getChildCount() > 0 && ppe.getChildAt(ppe.getChildCount() - 1).getEndPosition().compareTo(ppe.getEndPosition()) == 0 && ppe.getChildAt(ppe.getChildCount() - 1) instanceof NonTerminalProgramElement) {
                            ppe = (NonTerminalProgramElement) ppe.getChildAt(ppe.getChildCount() - 1);
                            dest = ppe;
                        }
                        c.setContainerComment(true);
                    }
                }
                if (!c.isContainerComment() && pe != dest)
                    if (pe.getFirstElement().getStartPosition().getLine() == dest.getLastElement().getEndPosition().getLine()) {
                        int before = c.getStartPosition().getColumn() - dest.getLastElement().getEndPosition().getColumn();
                        int after = pe.getFirstElement().getStartPosition().getColumn() - c.getEndPosition().getColumn();
                        if (after <= before) {
                            dest = pe;
                            c.setPrefixed(true);
                        }
                    }
            }
        }
        if (c.isPrefixed()) {
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
        if (c.isPrefixed() && c.getEndPosition().getLine() < dest.getStartPosition().getLine()) {
            NonTerminalProgramElement npe = dest.getASTParent();
            if (npe != null) {
                int idx = npe.getIndexOfChild(dest);
                if (idx > 0) {
                    int distPre = dest.getStartPosition().getLine() - c.getEndPosition().getLine();
                    int distPost = c.getStartPosition().getLine() - npe.getChildAt(idx - 1).getEndPosition().getLine();
                    if (c instanceof SingleLineComment)
                        distPost--;
                    if (distPost < distPre) {
                        dest = npe.getChildAt(idx - 1);
                        c.setPrefixed(false);
                    }
                }
            }
        } else if (!c.isPrefixed() && c.getStartPosition().getLine() > dest.getEndPosition().getLine()) {
            NonTerminalProgramElement npe = dest.getASTParent();
            if (npe != null) {
                int idx = npe.getIndexOfChild(dest);
                if (idx + 1 < npe.getChildCount()) {
                    int distPre = npe.getChildAt(idx + 1).getStartPosition().getLine() - c.getEndPosition().getLine();
                    int distPost = c.getStartPosition().getLine() - dest.getEndPosition().getLine();
                    if (c instanceof SingleLineComment)
                        distPost--;
                    if (distPre <= distPost) {
                        dest = npe.getChildAt(idx + 1);
                        c.setPrefixed(true);
                    }
                }
            }
        }
        if (c instanceof SingleLineComment && c.isPrefixed()) {
            SourceElement.Position p = dest.getFirstElement().getRelativePosition();
            if (p.getLine() < 1) {
                p.setLine(1);
                dest.getFirstElement().setRelativePosition(p);
            }
        }
        ASTList<Comment> cml = dest.getComments();
        if (cml == null)
            dest.setComments((ASTList<Comment>) (aSTArrayList = new ASTArrayList()));
        aSTArrayList.add(c);
    }

    private static void postWork(ProgramElement pe) {
        List<Comment> comments = JavaCCParser.getComments();
        int commentIndex = 0;
        int commentCount = comments.size();
        SourceElement.Position cpos = ZERO_POSITION;
        Comment current = null;
        if (commentIndex < commentCount) {
            current = comments.get(commentIndex);
            cpos = current.getFirstElement().getStartPosition();
        }
        TreeWalker tw = new TreeWalker(pe);
        while (tw.next()) {
            pe = tw.getProgramElement();
            if (pe instanceof NonTerminalProgramElement)
                ((NonTerminalProgramElement) pe).makeParentRoleValid();
            SourceElement.Position pos = pe.getFirstElement().getStartPosition();
            while (commentIndex < commentCount && pos.compareTo(cpos) > 0) {
                attachComment(current, pe);
                commentIndex++;
                if (commentIndex < commentCount) {
                    current = comments.get(commentIndex);
                    cpos = current.getFirstElement().getStartPosition();
                }
            }
        }
        if (commentIndex < commentCount) {
            while (pe.getASTParent() != null)
                pe = pe.getASTParent();
            do {
                ASTArrayList aSTArrayList;
                current = comments.get(commentIndex);
                ProgramElement dest = pe;
                ProgramElement newDest = null;
                while (dest instanceof NonTerminalProgramElement) {
                    NonTerminalProgramElement npe = (NonTerminalProgramElement) dest;
                    if (npe.getChildCount() == 0)
                        break;
                    newDest = npe.getChildAt(npe.getChildCount() - 1);
                    if ((npe.getEndPosition().compareTo(current.getStartPosition()) > 0 || (npe.getEndPosition().compareTo(current.getStartPosition()) == 0 && newDest.getEndPosition().compareTo(current.getStartPosition()) <= 0)) && dest != newDest)
                        dest = newDest;
                }
                ASTList<Comment> cml = dest.getComments();
                if (cml == null)
                    dest.setComments((ASTList<Comment>) (aSTArrayList = new ASTArrayList()));
                current.setPrefixed(false);
                aSTArrayList.add(current);
                ++commentIndex;
            } while (commentIndex < commentCount);
        }
    }

    public static int parseInt(String nm) throws NumberFormatException {
        int radix;
        boolean negative = false;
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
            index++;
            int i = Integer.valueOf(nm.substring(index), radix).intValue();
            i |= Character.digit(first, 16) << 28;
            return negative ? -i : i;
        }
        if (radix == 8 && len == 11) {
            char first = nm.charAt(index);
            index++;
            int i = Integer.valueOf(nm.substring(index), radix).intValue();
            i |= Character.digit(first, 8) << 30;
            return negative ? -i : i;
        }
        if (!negative && radix == 10 && len == 10 && nm.indexOf("2147483648", index) == index)
            return Integer.MIN_VALUE;
        int result = Integer.valueOf(nm.substring(index), radix).intValue();
        return negative ? -result : result;
    }

    public static long parseLong(String nm) throws NumberFormatException {
        int radix;
        if (nm.equalsIgnoreCase("0L"))
            return 0L;
        boolean negative = false;
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
        if (nm.endsWith("L") || nm.endsWith("l"))
            endIndex--;
        int len = endIndex - index;
        if (radix == 16 && len == 16) {
            char first = nm.charAt(index);
            index++;
            long l = Long.valueOf(nm.substring(index, endIndex), radix).longValue();
            l |= Character.digit(first, 16) << 60L;
            return negative ? -l : l;
        }
        if (radix == 8 && len == 21) {
            char first = nm.charAt(index);
            index++;
            long l = Long.valueOf(nm.substring(index, endIndex), radix).longValue();
            l |= (Character.digit(first, 8) << 63);
            return negative ? -l : l;
        }
        if (!negative && radix == 10 && len == 19 && nm.indexOf("9223372036854775808", index) == index)
            return Long.MIN_VALUE;
        long result = Long.valueOf(nm.substring(index, endIndex), radix).longValue();
        return negative ? -result : result;
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 1) {
            System.err.println("Requires a java source file as argument");
            System.exit(1);
        }
        try {
            CompilationUnit cu = (new DefaultServiceConfiguration()).getProgramFactory().parseCompilationUnit(new FileReader(args[0]));
            System.out.println(cu.toSource());
        } catch (IOException ioe) {
            System.err.println(ioe);
            ioe.printStackTrace();
        } catch (ParserException pe) {
            System.err.println(pe);
            pe.printStackTrace();
        }
    }

    public void initialize(ServiceConfiguration cfg) {
        serviceConfiguration = cfg;
        ProjectSettings settings = serviceConfiguration.getProjectSettings();
        settings.addPropertyChangeListener(this);
        writer = new StringWriter();
        sourcePrinter = new PrettyPrinter(writer, settings.getProperties());
        JavaCCParser.setAwareOfAssert(StringUtils.parseBooleanProperty(settings.getProperties().getProperty("jdk1.4")));
        JavaCCParser.setJava5(StringUtils.parseBooleanProperty(settings.getProperties().getProperty("java5")));
    }

    public ServiceConfiguration getServiceConfiguration() {
        return serviceConfiguration;
    }

    public CompilationUnit parseCompilationUnit(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(useAddNewlineReader ? new AddNewlineReader(in) : in);
            CompilationUnit res = JavaCCParser.CompilationUnit();
            postWork(res);
            return res;
        }
    }

    public TypeDeclaration parseTypeDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            TypeDeclaration res = JavaCCParser.TypeDeclaration();
            postWork(res);
            return res;
        }
    }

    public FieldDeclaration parseFieldDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            FieldDeclaration res = JavaCCParser.FieldDeclaration();
            postWork(res);
            return res;
        }
    }

    public MethodDeclaration parseMethodDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            MethodDeclaration res = JavaCCParser.MethodDeclaration();
            postWork(res);
            return res;
        }
    }

    public MemberDeclaration parseMemberDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            MemberDeclaration res = JavaCCParser.ClassBodyDeclaration();
            postWork(res);
            return res;
        }
    }

    public ParameterDeclaration parseParameterDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            ParameterDeclaration res = JavaCCParser.FormalParameter();
            postWork(res);
            return res;
        }
    }

    public ConstructorDeclaration parseConstructorDeclaration(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            ConstructorDeclaration res = JavaCCParser.ConstructorDeclaration();
            postWork(res);
            return res;
        }
    }

    public TypeReference parseTypeReference(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            TypeReference res = JavaCCParser.ResultType();
            postWork(res);
            return res;
        }
    }

    public Expression parseExpression(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            Expression res = JavaCCParser.Expression();
            postWork(res);
            return res;
        }
    }

    public ASTList<Statement> parseStatements(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            ASTList<Statement> res = JavaCCParser.GeneralizedStatements();
            for (int i = 0; i < res.size(); i++)
                postWork(res.get(i));
            return res;
        }
    }

    public StatementBlock parseStatementBlock(Reader in) throws IOException, ParserException {
        synchronized (parser) {
            JavaCCParser.initialize(in);
            StatementBlock res = JavaCCParser.Block();
            postWork(res);
            return res;
        }
    }

    public CompilationUnit parseCompilationUnit(String in) throws ParserException {
        try {
            return parseCompilationUnit(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

    public List<CompilationUnit> parseCompilationUnits(String[] ins) throws ParserException {
        try {
            List<CompilationUnit> cus = new ArrayList<CompilationUnit>();
            for (int i = 0; i < ins.length; i++) {
                CompilationUnit cu = parseCompilationUnit(new FileReader(ins[i]));
                cus.add(cu);
            }
            return cus;
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

    public TypeDeclaration parseTypeDeclaration(String in) throws ParserException {
        try {
            return parseTypeDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

    public MemberDeclaration parseMemberDeclaration(String in) throws ParserException {
        try {
            return parseMemberDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

    public FieldDeclaration parseFieldDeclaration(String in) throws ParserException {
        try {
            return parseFieldDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

    public MethodDeclaration parseMethodDeclaration(String in) throws ParserException {
        try {
            return parseMethodDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

    public ParameterDeclaration parseParameterDeclaration(String in) throws ParserException {
        try {
            return parseParameterDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

    public ConstructorDeclaration parseConstructorDeclaration(String in) throws ParserException {
        try {
            return parseConstructorDeclaration(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

    public TypeReference parseTypeReference(String in) throws ParserException {
        try {
            return parseTypeReference(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

    public Expression parseExpression(String in) throws ParserException {
        try {
            return parseExpression(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

    public ASTList<Statement> parseStatements(String in) throws ParserException {
        try {
            return parseStatements(new StringReader(in));
        } catch (IOException ioe) {
            throw new ParserException("" + ioe);
        }
    }

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

    public PrettyPrinter getPrettyPrinter(Writer out) {
        return new PrettyPrinter(out, serviceConfiguration.getProjectSettings().getProperties());
    }

    public void propertyChange(PropertyChangeEvent evt) {
        sourcePrinter = new PrettyPrinter(writer, serviceConfiguration.getProjectSettings().getProperties());
        String changedProp = evt.getPropertyName();
        if (changedProp.equals("jdk1.4"))
            JavaCCParser.setAwareOfAssert(StringUtils.parseBooleanProperty(evt.getNewValue().toString()));
        if (changedProp.equals("java5"))
            JavaCCParser.setJava5(StringUtils.parseBooleanProperty(evt.getNewValue().toString()));
        if (changedProp.equals("extra_newline_at_end_of_file"))
            useAddNewlineReader = StringUtils.parseBooleanProperty(evt.getNewValue().toString());
    }

    public Comment createComment() {
        return new Comment();
    }

    public Comment createComment(String text) {
        return new Comment(text);
    }

    public Comment createComment(String text, boolean prefixed) {
        return new Comment(text, prefixed);
    }

    public CompilationUnit createCompilationUnit() {
        return new CompilationUnit();
    }

    public CompilationUnit createCompilationUnit(PackageSpecification pkg, ASTList<Import> imports, ASTList<TypeDeclaration> typeDeclarations) {
        return new CompilationUnit(pkg, imports, typeDeclarations);
    }

    public DocComment createDocComment() {
        return new DocComment();
    }

    public DocComment createDocComment(String text) {
        return new DocComment(text);
    }

    public Identifier createIdentifier() {
        return new Identifier();
    }

    public Identifier createIdentifier(String text) {
        return new Identifier(text);
    }

    public Import createImport() {
        return new Import();
    }

    public Import createImport(TypeReference t, boolean multi) {
        return new Import(t, multi);
    }

    public Import createImport(PackageReference t) {
        return new Import(t);
    }

    public Import createStaticImport(TypeReference t) {
        return new Import(t, true, true);
    }

    public Import createStaticImport(TypeReference t, Identifier id) {
        return new Import(t, id);
    }

    public PackageSpecification createPackageSpecification() {
        return new PackageSpecification();
    }

    public PackageSpecification createPackageSpecification(PackageReference pkg) {
        return new PackageSpecification(pkg);
    }

    public SingleLineComment createSingleLineComment() {
        return new SingleLineComment();
    }

    public SingleLineComment createSingleLineComment(String text) {
        return new SingleLineComment(text);
    }

    public TypeReference createTypeReference() {
        return new TypeReference();
    }

    public TypeReference createTypeReference(Identifier name) {
        return new TypeReference(name);
    }

    public TypeReference createTypeReference(ReferencePrefix prefix, Identifier name) {
        return new TypeReference(prefix, name);
    }

    public TypeReference createTypeReference(Identifier name, int dim) {
        return new TypeReference(name, dim);
    }

    public PackageReference createPackageReference() {
        return new PackageReference();
    }

    public PackageReference createPackageReference(Identifier id) {
        return new PackageReference(id);
    }

    public PackageReference createPackageReference(PackageReference path, Identifier id) {
        return new PackageReference(path, id);
    }

    public UncollatedReferenceQualifier createUncollatedReferenceQualifier() {
        return new UncollatedReferenceQualifier();
    }

    public UncollatedReferenceQualifier createUncollatedReferenceQualifier(Identifier id) {
        return new UncollatedReferenceQualifier(id);
    }

    public UncollatedReferenceQualifier createUncollatedReferenceQualifier(ReferencePrefix prefix, Identifier id) {
        return new UncollatedReferenceQualifier(prefix, id);
    }

    public ClassDeclaration createClassDeclaration() {
        return new ClassDeclaration();
    }

    public ClassDeclaration createClassDeclaration(ASTList<DeclarationSpecifier> declSpecs, Identifier name, Extends extended, Implements implemented, ASTList<MemberDeclaration> members) {
        return new ClassDeclaration(declSpecs, name, extended, implemented, members);
    }

    public ClassDeclaration createClassDeclaration(ASTList<MemberDeclaration> members) {
        return new ClassDeclaration(members);
    }

    public ClassInitializer createClassInitializer() {
        return new ClassInitializer();
    }

    public ClassInitializer createClassInitializer(StatementBlock body) {
        return new ClassInitializer(body);
    }

    public ClassInitializer createClassInitializer(Static modifier, StatementBlock body) {
        return new ClassInitializer(modifier, body);
    }

    public ConstructorDeclaration createConstructorDeclaration() {
        return new ConstructorDeclaration();
    }

    public ConstructorDeclaration createConstructorDeclaration(VisibilityModifier modifier, Identifier name, ASTList<ParameterDeclaration> parameters, Throws exceptions, StatementBlock body) {
        return new ConstructorDeclaration(modifier, name, parameters, exceptions, body);
    }

    public Throws createThrows() {
        return new Throws();
    }

    public Throws createThrows(TypeReference exception) {
        return new Throws(exception);
    }

    public Throws createThrows(ASTList<TypeReference> list) {
        return new Throws(list);
    }

    public FieldDeclaration createFieldDeclaration() {
        return new FieldDeclaration();
    }

    public FieldDeclaration createFieldDeclaration(TypeReference typeRef, Identifier name) {
        return new FieldDeclaration(typeRef, name);
    }

    public FieldDeclaration createFieldDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, Identifier name, Expression init) {
        return new FieldDeclaration(mods, typeRef, name, init);
    }

    public FieldDeclaration createFieldDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, ASTList<FieldSpecification> vars) {
        return new FieldDeclaration(mods, typeRef, vars);
    }

    public Extends createExtends() {
        return new Extends();
    }

    public Extends createExtends(TypeReference supertype) {
        return new Extends(supertype);
    }

    public Extends createExtends(ASTList<TypeReference> list) {
        return new Extends(list);
    }

    public Implements createImplements() {
        return new Implements();
    }

    public Implements createImplements(TypeReference supertype) {
        return new Implements(supertype);
    }

    public Implements createImplements(ASTList<TypeReference> list) {
        return new Implements(list);
    }

    public InterfaceDeclaration createInterfaceDeclaration() {
        return new InterfaceDeclaration();
    }

    public InterfaceDeclaration createInterfaceDeclaration(ASTList<DeclarationSpecifier> modifiers, Identifier name, Extends extended, ASTList<MemberDeclaration> members) {
        return new InterfaceDeclaration(modifiers, name, extended, members);
    }

    public AnnotationDeclaration createAnnotationDeclaration() {
        return new AnnotationDeclaration();
    }

    public AnnotationDeclaration createAnnotationDeclaration(ASTList<DeclarationSpecifier> modifiers, Identifier name, ASTList<MemberDeclaration> members) {
        return new AnnotationDeclaration(modifiers, name, members);
    }

    public LocalVariableDeclaration createLocalVariableDeclaration() {
        return new LocalVariableDeclaration();
    }

    public LocalVariableDeclaration createLocalVariableDeclaration(TypeReference typeRef, Identifier name) {
        return new LocalVariableDeclaration(typeRef, name);
    }

    public LocalVariableDeclaration createLocalVariableDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, ASTList<VariableSpecification> vars) {
        return new LocalVariableDeclaration(mods, typeRef, vars);
    }

    public LocalVariableDeclaration createLocalVariableDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, Identifier name, Expression init) {
        return new LocalVariableDeclaration(mods, typeRef, name, init);
    }

    public MethodDeclaration createMethodDeclaration() {
        return new MethodDeclaration();
    }

    public MethodDeclaration createMethodDeclaration(ASTList<DeclarationSpecifier> modifiers, TypeReference returnType, Identifier name, ASTList<ParameterDeclaration> parameters, Throws exceptions) {
        return new MethodDeclaration(modifiers, returnType, name, parameters, exceptions);
    }

    public MethodDeclaration createMethodDeclaration(ASTList<DeclarationSpecifier> modifiers, TypeReference returnType, Identifier name, ASTList<ParameterDeclaration> parameters, Throws exceptions, StatementBlock body) {
        return new MethodDeclaration(modifiers, returnType, name, parameters, exceptions, body);
    }

    public AnnotationPropertyDeclaration createAnnotationPropertyDeclaration(ASTList<DeclarationSpecifier> modifiers, TypeReference returnType, Identifier name, Expression defaultValue) {
        return new AnnotationPropertyDeclaration(modifiers, returnType, name, defaultValue);
    }

    public ParameterDeclaration createParameterDeclaration() {
        return new ParameterDeclaration();
    }

    public ParameterDeclaration createParameterDeclaration(TypeReference typeRef, Identifier name) {
        return new ParameterDeclaration(typeRef, name);
    }

    public ParameterDeclaration createParameterDeclaration(ASTList<DeclarationSpecifier> mods, TypeReference typeRef, Identifier name) {
        return new ParameterDeclaration(mods, typeRef, name);
    }

    public VariableSpecification createVariableSpecification() {
        return new VariableSpecification();
    }

    public VariableSpecification createVariableSpecification(Identifier name) {
        return new VariableSpecification(name);
    }

    public VariableSpecification createVariableSpecification(Identifier name, Expression init) {
        return new VariableSpecification(name, init);
    }

    public VariableSpecification createVariableSpecification(Identifier name, int dimensions, Expression init) {
        return new VariableSpecification(name, dimensions, init);
    }

    public FieldSpecification createFieldSpecification() {
        return new FieldSpecification();
    }

    public FieldSpecification createFieldSpecification(Identifier name) {
        return new FieldSpecification(name);
    }

    public FieldSpecification createFieldSpecification(Identifier name, Expression init) {
        return new FieldSpecification(name, init);
    }

    public FieldSpecification createFieldSpecification(Identifier name, int dimensions, Expression init) {
        return new FieldSpecification(name, dimensions, init);
    }

    public ArrayInitializer createArrayInitializer() {
        return new ArrayInitializer();
    }

    public ArrayInitializer createArrayInitializer(ASTList<Expression> args) {
        return new ArrayInitializer(args);
    }

    public ParenthesizedExpression createParenthesizedExpression() {
        return new ParenthesizedExpression();
    }

    public ParenthesizedExpression createParenthesizedExpression(Expression child) {
        return new ParenthesizedExpression(child);
    }

    public BooleanLiteral createBooleanLiteral() {
        return new BooleanLiteral();
    }

    public BooleanLiteral createBooleanLiteral(boolean value) {
        return new BooleanLiteral(value);
    }

    public CharLiteral createCharLiteral() {
        return new CharLiteral();
    }

    public CharLiteral createCharLiteral(char value) {
        return new CharLiteral(value);
    }

    public CharLiteral createCharLiteral(String value) {
        return new CharLiteral(value);
    }

    public DoubleLiteral createDoubleLiteral() {
        return new DoubleLiteral();
    }

    public DoubleLiteral createDoubleLiteral(double value) {
        return new DoubleLiteral(value);
    }

    public DoubleLiteral createDoubleLiteral(String value) {
        return new DoubleLiteral(value);
    }

    public FloatLiteral createFloatLiteral() {
        return new FloatLiteral();
    }

    public FloatLiteral createFloatLiteral(float value) {
        return new FloatLiteral(value);
    }

    public FloatLiteral createFloatLiteral(String value) {
        return new FloatLiteral(value);
    }

    public IntLiteral createIntLiteral() {
        return new IntLiteral();
    }

    public IntLiteral createIntLiteral(int value) {
        return new IntLiteral(value);
    }

    public IntLiteral createIntLiteral(String value) {
        return new IntLiteral(value);
    }

    public LongLiteral createLongLiteral() {
        return new LongLiteral();
    }

    public LongLiteral createLongLiteral(long value) {
        return new LongLiteral(value);
    }

    public LongLiteral createLongLiteral(String value) {
        return new LongLiteral(value);
    }

    public NullLiteral createNullLiteral() {
        return new NullLiteral();
    }

    public StringLiteral createStringLiteral() {
        return new StringLiteral();
    }

    public StringLiteral createStringLiteral(String value) {
        return new StringLiteral(value);
    }

    public ArrayReference createArrayReference() {
        return new ArrayReference();
    }

    public ArrayReference createArrayReference(ReferencePrefix accessPath, ASTList<Expression> initializers) {
        return new ArrayReference(accessPath, initializers);
    }

    public FieldReference createFieldReference() {
        return new FieldReference();
    }

    public FieldReference createFieldReference(Identifier id) {
        return new FieldReference(id);
    }

    public FieldReference createFieldReference(ReferencePrefix prefix, Identifier id) {
        return new FieldReference(prefix, id);
    }

    public MetaClassReference createMetaClassReference() {
        return new MetaClassReference();
    }

    public MetaClassReference createMetaClassReference(TypeReference reference) {
        return new MetaClassReference(reference);
    }

    public MethodReference createMethodReference() {
        return new MethodReference();
    }

    public MethodReference createMethodReference(Identifier name) {
        return new MethodReference(name);
    }

    public MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name) {
        return new MethodReference(accessPath, name);
    }

    public MethodReference createMethodReference(Identifier name, ASTList<Expression> args) {
        return new MethodReference(name, args);
    }

    public MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name, ASTList<Expression> args) {
        return new MethodReference(accessPath, name, args);
    }

    public MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name, ASTList<Expression> args, ASTList<TypeArgumentDeclaration> typeArgs) {
        return new MethodReference(accessPath, name, args, typeArgs);
    }

    public AnnotationPropertyReference createAnnotationPropertyReference(String id) {
        Identifier ident = new Identifier(id);
        return new AnnotationPropertyReference(ident);
    }

    public AnnotationPropertyReference createAnnotationPropertyReference(Identifier id) {
        return new AnnotationPropertyReference(id);
    }

    public SuperConstructorReference createSuperConstructorReference() {
        return new SuperConstructorReference();
    }

    public SuperConstructorReference createSuperConstructorReference(ASTList<Expression> arguments) {
        return new SuperConstructorReference(arguments);
    }

    public SuperConstructorReference createSuperConstructorReference(ReferencePrefix path, ASTList<Expression> arguments) {
        return new SuperConstructorReference(path, arguments);
    }

    public SuperReference createSuperReference() {
        return new SuperReference();
    }

    public SuperReference createSuperReference(ReferencePrefix accessPath) {
        return new SuperReference(accessPath);
    }

    public ThisConstructorReference createThisConstructorReference() {
        return new ThisConstructorReference();
    }

    public ThisConstructorReference createThisConstructorReference(ASTList<Expression> arguments) {
        return new ThisConstructorReference(arguments);
    }

    public ThisReference createThisReference() {
        return new ThisReference();
    }

    public ThisReference createThisReference(TypeReference outer) {
        return new ThisReference(outer);
    }

    public VariableReference createVariableReference() {
        return new VariableReference();
    }

    public VariableReference createVariableReference(Identifier id) {
        return new VariableReference(id);
    }

    public ArrayLengthReference createArrayLengthReference() {
        return new ArrayLengthReference();
    }

    public ArrayLengthReference createArrayLengthReference(ReferencePrefix prefix) {
        return new ArrayLengthReference(prefix);
    }

    public BinaryAnd createBinaryAnd() {
        return new BinaryAnd();
    }

    public BinaryAnd createBinaryAnd(Expression lhs, Expression rhs) {
        return new BinaryAnd(lhs, rhs);
    }

    public BinaryAndAssignment createBinaryAndAssignment() {
        return new BinaryAndAssignment();
    }

    public BinaryAndAssignment createBinaryAndAssignment(Expression lhs, Expression rhs) {
        return new BinaryAndAssignment(lhs, rhs);
    }

    public BinaryNot createBinaryNot() {
        return new BinaryNot();
    }

    public BinaryNot createBinaryNot(Expression child) {
        return new BinaryNot(child);
    }

    public BinaryOr createBinaryOr() {
        return new BinaryOr();
    }

    public BinaryOr createBinaryOr(Expression lhs, Expression rhs) {
        return new BinaryOr(lhs, rhs);
    }

    public BinaryOrAssignment createBinaryOrAssignment() {
        return new BinaryOrAssignment();
    }

    public BinaryOrAssignment createBinaryOrAssignment(Expression lhs, Expression rhs) {
        return new BinaryOrAssignment(lhs, rhs);
    }

    public BinaryXOr createBinaryXOr() {
        return new BinaryXOr();
    }

    public BinaryXOr createBinaryXOr(Expression lhs, Expression rhs) {
        return new BinaryXOr(lhs, rhs);
    }

    public BinaryXOrAssignment createBinaryXOrAssignment() {
        return new BinaryXOrAssignment();
    }

    public BinaryXOrAssignment createBinaryXOrAssignment(Expression lhs, Expression rhs) {
        return new BinaryXOrAssignment(lhs, rhs);
    }

    public Conditional createConditional() {
        return new Conditional();
    }

    public Conditional createConditional(Expression guard, Expression thenExpr, Expression elseExpr) {
        return new Conditional(guard, thenExpr, elseExpr);
    }

    public CopyAssignment createCopyAssignment() {
        return new CopyAssignment();
    }

    public CopyAssignment createCopyAssignment(Expression lhs, Expression rhs) {
        return new CopyAssignment(lhs, rhs);
    }

    public Divide createDivide() {
        return new Divide();
    }

    public Divide createDivide(Expression lhs, Expression rhs) {
        return new Divide(lhs, rhs);
    }

    public DivideAssignment createDivideAssignment() {
        return new DivideAssignment();
    }

    public DivideAssignment createDivideAssignment(Expression lhs, Expression rhs) {
        return new DivideAssignment(lhs, rhs);
    }

    public Equals createEquals() {
        return new Equals();
    }

    public Equals createEquals(Expression lhs, Expression rhs) {
        return new Equals(lhs, rhs);
    }

    public GreaterOrEquals createGreaterOrEquals() {
        return new GreaterOrEquals();
    }

    public GreaterOrEquals createGreaterOrEquals(Expression lhs, Expression rhs) {
        return new GreaterOrEquals(lhs, rhs);
    }

    public GreaterThan createGreaterThan() {
        return new GreaterThan();
    }

    public GreaterThan createGreaterThan(Expression lhs, Expression rhs) {
        return new GreaterThan(lhs, rhs);
    }

    public Instanceof createInstanceof() {
        return new Instanceof();
    }

    public Instanceof createInstanceof(Expression child, TypeReference typeref) {
        return new Instanceof(child, typeref);
    }

    public LessOrEquals createLessOrEquals() {
        return new LessOrEquals();
    }

    public LessOrEquals createLessOrEquals(Expression lhs, Expression rhs) {
        return new LessOrEquals(lhs, rhs);
    }

    public LessThan createLessThan() {
        return new LessThan();
    }

    public LessThan createLessThan(Expression lhs, Expression rhs) {
        return new LessThan(lhs, rhs);
    }

    public LogicalAnd createLogicalAnd() {
        return new LogicalAnd();
    }

    public LogicalAnd createLogicalAnd(Expression lhs, Expression rhs) {
        return new LogicalAnd(lhs, rhs);
    }

    public LogicalNot createLogicalNot() {
        return new LogicalNot();
    }

    public LogicalNot createLogicalNot(Expression child) {
        return new LogicalNot(child);
    }

    public LogicalOr createLogicalOr() {
        return new LogicalOr();
    }

    public LogicalOr createLogicalOr(Expression lhs, Expression rhs) {
        return new LogicalOr(lhs, rhs);
    }

    public Minus createMinus() {
        return new Minus();
    }

    public Minus createMinus(Expression lhs, Expression rhs) {
        return new Minus(lhs, rhs);
    }

    public MinusAssignment createMinusAssignment() {
        return new MinusAssignment();
    }

    public MinusAssignment createMinusAssignment(Expression lhs, Expression rhs) {
        return new MinusAssignment(lhs, rhs);
    }

    public Modulo createModulo() {
        return new Modulo();
    }

    public Modulo createModulo(Expression lhs, Expression rhs) {
        return new Modulo(lhs, rhs);
    }

    public ModuloAssignment createModuloAssignment() {
        return new ModuloAssignment();
    }

    public ModuloAssignment createModuloAssignment(Expression lhs, Expression rhs) {
        return new ModuloAssignment(lhs, rhs);
    }

    public Negative createNegative() {
        return new Negative();
    }

    public Negative createNegative(Expression child) {
        return new Negative(child);
    }

    public New createNew() {
        return new New();
    }

    public New createNew(ReferencePrefix accessPath, TypeReference constructorName, ASTList<Expression> arguments) {
        return new New(accessPath, constructorName, arguments);
    }

    public New createNew(ReferencePrefix accessPath, TypeReference constructorName, ASTList<Expression> arguments, ClassDeclaration anonymousClass) {
        return new New(accessPath, constructorName, arguments, anonymousClass);
    }

    public NewArray createNewArray() {
        return new NewArray();
    }

    public NewArray createNewArray(TypeReference arrayName, ASTList<Expression> dimExpr) {
        return new NewArray(arrayName, dimExpr);
    }

    public NewArray createNewArray(TypeReference arrayName, int dimensions, ArrayInitializer initializer) {
        return new NewArray(arrayName, dimensions, initializer);
    }

    public NotEquals createNotEquals() {
        return new NotEquals();
    }

    public NotEquals createNotEquals(Expression lhs, Expression rhs) {
        return new NotEquals(lhs, rhs);
    }

    public Plus createPlus() {
        return new Plus();
    }

    public Plus createPlus(Expression lhs, Expression rhs) {
        return new Plus(lhs, rhs);
    }

    public PlusAssignment createPlusAssignment() {
        return new PlusAssignment();
    }

    public PlusAssignment createPlusAssignment(Expression lhs, Expression rhs) {
        return new PlusAssignment(lhs, rhs);
    }

    public Positive createPositive() {
        return new Positive();
    }

    public Positive createPositive(Expression child) {
        return new Positive(child);
    }

    public PostDecrement createPostDecrement() {
        return new PostDecrement();
    }

    public PostDecrement createPostDecrement(Expression child) {
        return new PostDecrement(child);
    }

    public PostIncrement createPostIncrement() {
        return new PostIncrement();
    }

    public PostIncrement createPostIncrement(Expression child) {
        return new PostIncrement(child);
    }

    public PreDecrement createPreDecrement() {
        return new PreDecrement();
    }

    public PreDecrement createPreDecrement(Expression child) {
        return new PreDecrement(child);
    }

    public PreIncrement createPreIncrement() {
        return new PreIncrement();
    }

    public PreIncrement createPreIncrement(Expression child) {
        return new PreIncrement(child);
    }

    public ShiftLeft createShiftLeft() {
        return new ShiftLeft();
    }

    public ShiftLeft createShiftLeft(Expression lhs, Expression rhs) {
        return new ShiftLeft(lhs, rhs);
    }

    public ShiftLeftAssignment createShiftLeftAssignment() {
        return new ShiftLeftAssignment();
    }

    public ShiftLeftAssignment createShiftLeftAssignment(Expression lhs, Expression rhs) {
        return new ShiftLeftAssignment(lhs, rhs);
    }

    public ShiftRight createShiftRight() {
        return new ShiftRight();
    }

    public ShiftRight createShiftRight(Expression lhs, Expression rhs) {
        return new ShiftRight(lhs, rhs);
    }

    public ShiftRightAssignment createShiftRightAssignment() {
        return new ShiftRightAssignment();
    }

    public ShiftRightAssignment createShiftRightAssignment(Expression lhs, Expression rhs) {
        return new ShiftRightAssignment(lhs, rhs);
    }

    public Times createTimes() {
        return new Times();
    }

    public Times createTimes(Expression lhs, Expression rhs) {
        return new Times(lhs, rhs);
    }

    public TimesAssignment createTimesAssignment() {
        return new TimesAssignment();
    }

    public TimesAssignment createTimesAssignment(Expression lhs, Expression rhs) {
        return new TimesAssignment(lhs, rhs);
    }

    public TypeCast createTypeCast() {
        return new TypeCast();
    }

    public TypeCast createTypeCast(Expression child, TypeReference typeref) {
        return new TypeCast(child, typeref);
    }

    public UnsignedShiftRight createUnsignedShiftRight() {
        return new UnsignedShiftRight();
    }

    public UnsignedShiftRight createUnsignedShiftRight(Expression lhs, Expression rhs) {
        return new UnsignedShiftRight(lhs, rhs);
    }

    public UnsignedShiftRightAssignment createUnsignedShiftRightAssignment() {
        return new UnsignedShiftRightAssignment();
    }

    public UnsignedShiftRightAssignment createUnsignedShiftRightAssignment(Expression lhs, Expression rhs) {
        return new UnsignedShiftRightAssignment(lhs, rhs);
    }

    public Abstract createAbstract() {
        return new Abstract();
    }

    public Final createFinal() {
        return new Final();
    }

    public Native createNative() {
        return new Native();
    }

    public Private createPrivate() {
        return new Private();
    }

    public Protected createProtected() {
        return new Protected();
    }

    public Public createPublic() {
        return new Public();
    }

    public Static createStatic() {
        return new Static();
    }

    public Synchronized createSynchronized() {
        return new Synchronized();
    }

    public Transient createTransient() {
        return new Transient();
    }

    public StrictFp createStrictFp() {
        return new StrictFp();
    }

    public Volatile createVolatile() {
        return new Volatile();
    }

    public AnnotationUseSpecification createAnnotationUseSpecification() {
        return new AnnotationUseSpecification();
    }

    public Break createBreak() {
        return new Break();
    }

    public Break createBreak(Identifier label) {
        return new Break(label);
    }

    public Case createCase() {
        return new Case();
    }

    public Case createCase(Expression e) {
        return new Case(e);
    }

    public Case createCase(Expression e, ASTList<Statement> body) {
        return new Case(e, body);
    }

    public Catch createCatch() {
        return new Catch();
    }

    public Catch createCatch(ParameterDeclaration e, StatementBlock body) {
        return new Catch(e, body);
    }

    public Continue createContinue() {
        return new Continue();
    }

    public Continue createContinue(Identifier label) {
        return new Continue(label);
    }

    public Default createDefault() {
        return new Default();
    }

    public Default createDefault(ASTList<Statement> body) {
        return new Default(body);
    }

    public Do createDo() {
        return new Do();
    }

    public Do createDo(Expression guard) {
        return new Do(guard);
    }

    public Do createDo(Expression guard, Statement body) {
        return new Do(guard, body);
    }

    public Else createElse() {
        return new Else();
    }

    public Else createElse(Statement body) {
        return new Else(body);
    }

    public EmptyStatement createEmptyStatement() {
        return new EmptyStatement();
    }

    public Finally createFinally() {
        return new Finally();
    }

    public Finally createFinally(StatementBlock body) {
        return new Finally(body);
    }

    public For createFor() {
        return new For();
    }

    public For createFor(ASTList<LoopInitializer> inits, Expression guard, ASTList<Expression> updates, Statement body) {
        return new For(inits, guard, updates, body);
    }

    public EnhancedFor createEnhancedFor() {
        return new EnhancedFor();
    }

    public Assert createAssert() {
        return new Assert();
    }

    public Assert createAssert(Expression cond) {
        return new Assert(cond);
    }

    public Assert createAssert(Expression cond, Expression msg) {
        return new Assert(cond, msg);
    }

    public If createIf() {
        return new If();
    }

    public If createIf(Expression e, Statement thenStatement) {
        return new If(e, thenStatement);
    }

    public If createIf(Expression e, Then thenBranch) {
        return new If(e, thenBranch);
    }

    public If createIf(Expression e, Then thenBranch, Else elseBranch) {
        return new If(e, thenBranch, elseBranch);
    }

    public If createIf(Expression e, Statement thenStatement, Statement elseStatement) {
        return new If(e, thenStatement, elseStatement);
    }

    public LabeledStatement createLabeledStatement() {
        return new LabeledStatement();
    }

    public LabeledStatement createLabeledStatement(Identifier id) {
        return new LabeledStatement(id);
    }

    public LabeledStatement createLabeledStatement(Identifier id, Statement statement) {
        return new LabeledStatement(id, statement);
    }

    public Return createReturn() {
        return new Return();
    }

    public Return createReturn(Expression expr) {
        return new Return(expr);
    }

    public StatementBlock createStatementBlock() {
        return new StatementBlock();
    }

    public StatementBlock createStatementBlock(ASTList<Statement> block) {
        return new StatementBlock(block);
    }

    public Switch createSwitch() {
        return new Switch();
    }

    public Switch createSwitch(Expression e) {
        return new Switch(e);
    }

    public Switch createSwitch(Expression e, ASTList<Branch> branches) {
        return new Switch(e, branches);
    }

    public SynchronizedBlock createSynchronizedBlock() {
        return new SynchronizedBlock();
    }

    public SynchronizedBlock createSynchronizedBlock(StatementBlock body) {
        return new SynchronizedBlock(body);
    }

    public SynchronizedBlock createSynchronizedBlock(Expression e, StatementBlock body) {
        return new SynchronizedBlock(e, body);
    }

    public Then createThen() {
        return new Then();
    }

    public Then createThen(Statement body) {
        return new Then(body);
    }

    public Throw createThrow() {
        return new Throw();
    }

    public Throw createThrow(Expression expr) {
        return new Throw(expr);
    }

    public Try createTry() {
        return new Try();
    }

    public Try createTry(StatementBlock body) {
        return new Try(body);
    }

    public Try createTry(StatementBlock body, ASTList<Branch> branches) {
        return new Try(body, branches);
    }

    public While createWhile() {
        return new While();
    }

    public While createWhile(Expression guard) {
        return new While(guard);
    }

    public While createWhile(Expression guard, Statement body) {
        return new While(guard, body);
    }

    private class AddNewlineReader extends Reader {
        private final Reader reader;

        private boolean added;

        AddNewlineReader(Reader reader) {
            this.added = false;
            this.reader = reader;
        }

        public void mark(int readAheadLimit) throws IOException {
            this.reader.mark(readAheadLimit);
        }

        public boolean markSupported() {
            return this.reader.markSupported();
        }

        public int read() throws IOException {
            return this.reader.read();
        }

        public int read(char[] cbuf) throws IOException {
            return this.reader.read(cbuf);
        }

        public int read(CharBuffer target) throws IOException {
            return this.reader.read(target);
        }

        public boolean ready() throws IOException {
            return this.reader.ready();
        }

        public void reset() throws IOException {
            this.reader.reset();
        }

        public long skip(long n) throws IOException {
            return this.reader.skip(n);
        }

        public void close() throws IOException {
            this.reader.close();
        }

        public int read(char[] cbuf, int off, int len) throws IOException {
            if (this.added)
                return -1;
            int result = this.reader.read(cbuf, off, len);
            if (!this.added && result < len) {
                if (result == -1)
                    result++;
                cbuf[off + result++] = '\n';
                this.added = true;
            }
            return result;
        }
    }
}
