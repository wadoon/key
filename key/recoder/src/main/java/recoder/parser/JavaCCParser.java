package recoder.parser;

import recoder.abstraction.TypeArgument;
import recoder.convenience.Format;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.*;
import recoder.java.expression.*;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

import java.io.InputStream;
import java.io.Reader;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.Vector;

public class JavaCCParser implements JavaCCParserConstants {
    private static final int[] jj_la1 = new int[173];
    private static final JJCalls[] jj_2_rtns = new JJCalls[62];
    private static final LookaheadSuccess jj_ls = new LookaheadSuccess();
    public static JavaCCParserTokenManager token_source;
    public static Token token;
    public static Token jj_nt;
    public static boolean lookingAhead = false;
    static boolean superAllowed = true;
    static boolean jdk1_4 = false;
    static boolean jdk1_5 = false;
    static PrimarySuffixReturnValue suffix = new PrimarySuffixReturnValue();
    static PrimaryPrefixReturnValue prefix = new PrimaryPrefixReturnValue();
    static JavaCharStream jj_input_stream;
    private static final JavaProgramFactory factory = JavaProgramFactory.getInstance();
    private static int tmpDimension;
    private static Token current;
    private static final List<Comment> comments = new ArrayList<Comment>();
    private static final SourceElement.Position position = new SourceElement.Position(0, 0);
    private static boolean jj_initialized_once = false;
    private static int jj_ntk;
    private static Token jj_scanpos;
    private static Token jj_lastpos;
    private static int jj_la;
    private static boolean jj_semLA;
    private static int jj_gen;
    private static int[] jj_la1_0;
    private static int[] jj_la1_1;
    private static int[] jj_la1_2;
    private static int[] jj_la1_3;
    private static boolean jj_rescan = false;
    private static int jj_gc = 0;
    private static final Vector jj_expentries = new Vector();
    private static int[] jj_expentry;
    private static int jj_kind = -1;
    private static final int[] jj_lasttokens = new int[100];
    private static int jj_endpos;

    static {
        jj_la1_0();
        jj_la1_1();
        jj_la1_2();
        jj_la1_3();
    }

    public JavaCCParser(InputStream stream) {
        this(stream, null);
    }

    public JavaCCParser(InputStream stream, String encoding) {
        if (jj_initialized_once) {
            System.out.println("ERROR: Second call to constructor of static parser.  You must");
            System.out.println("       either use ReInit() or set the JavaCC option STATIC to false");
            System.out.println("       during parser generation.");
            throw new Error();
        }
        jj_initialized_once = true;
        try {
            jj_input_stream = new JavaCharStream(stream, encoding, 1, 1);
        } catch (UnsupportedEncodingException e) {
            throw new RuntimeException(e);
        }
        token_source = new JavaCCParserTokenManager(jj_input_stream);
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        int i;
        for (i = 0; i < 173; ) {
            jj_la1[i] = -1;
            i++;
        }
        for (i = 0; i < jj_2_rtns.length; ) {
            jj_2_rtns[i] = new JJCalls();
            i++;
        }
    }

    public JavaCCParser(Reader stream) {
        if (jj_initialized_once) {
            System.out.println("ERROR: Second call to constructor of static parser.  You must");
            System.out.println("       either use ReInit() or set the JavaCC option STATIC to false");
            System.out.println("       during parser generation.");
            throw new Error();
        }
        jj_initialized_once = true;
        jj_input_stream = new JavaCharStream(stream, 1, 1);
        token_source = new JavaCCParserTokenManager(jj_input_stream);
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        int i;
        for (i = 0; i < 173; ) {
            jj_la1[i] = -1;
            i++;
        }
        for (i = 0; i < jj_2_rtns.length; ) {
            jj_2_rtns[i] = new JJCalls();
            i++;
        }
    }

    public JavaCCParser(JavaCCParserTokenManager tm) {
        if (jj_initialized_once) {
            System.out.println("ERROR: Second call to constructor of static parser.  You must");
            System.out.println("       either use ReInit() or set the JavaCC option STATIC to false");
            System.out.println("       during parser generation.");
            throw new Error();
        }
        jj_initialized_once = true;
        token_source = tm;
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        int i;
        for (i = 0; i < 173; ) {
            jj_la1[i] = -1;
            i++;
        }
        for (i = 0; i < jj_2_rtns.length; ) {
            jj_2_rtns[i] = new JJCalls();
            i++;
        }
    }

    public static final void initialize(Reader r) {
        current = null;
        comments.clear();
        ReInit(r);
    }

    private static boolean isSuperAllowed() {
        return superAllowed;
    }

    private static void setAllowSuper(boolean b) {
        superAllowed = b;
    }

    public static boolean isAwareOfAssert() {
        return jdk1_4;
    }

    public static void setAwareOfAssert(boolean yes) {
        jdk1_4 = yes;
        if (!yes)
            jdk1_5 = false;
    }

    public static boolean isJava5() {
        return jdk1_5;
    }

    public static void setJava5(boolean yes) {
        jdk1_5 = yes;
        if (yes)
            jdk1_4 = true;
    }

    public static int getTabSize() {
        return JavaCharStream.getTabSize(0);
    }

    public static void setTabSize(int tabSize) {
        JavaCharStream.setTabSize(tabSize);
    }

    private static void copyPrefixInfo(SourceElement oldResult, SourceElement newResult) {
        newResult.setRelativePosition(oldResult.getRelativePosition());
        newResult.setStartPosition(oldResult.getStartPosition());
        newResult.setEndPosition(oldResult.getEndPosition());
    }

    private static void shiftToken() {
        if (current != token) {
            Token prev;
            if (current != null)
                while (current.next != token)
                    current = current.next;
            if (token.specialToken != null) {
                prev = token.specialToken;
            } else {
                prev = current;
            }
            if (prev != null) {
                int col = token.beginColumn - 1;
                int lf = token.beginLine - prev.endLine;
                if (lf <= 0) {
                    col -= prev.endColumn;
                    if (col < 0)
                        col = 0;
                }
                position.setPosition(lf, col);
            }
            current = token;
        }
    }

    private static void setPrefixInfo(SourceElement constrResult) {
        position.setPosition(0, 0);
        shiftToken();
        constrResult.setRelativePosition(position);
        position.setPosition(current.beginLine, current.beginColumn);
        constrResult.setStartPosition(position);
    }

    private static void setPostfixInfo(SourceElement constrResult) {
        shiftToken();
        position.setPosition(current.endLine, current.endColumn);
        constrResult.setEndPosition(position);
    }

    private static void addComment(Comment c, Token tok) {
        Token prev = tok.specialToken;
        if (prev == null) {
            prev = token;
            while (prev.next != null)
                prev = prev.next;
        }
        position.setPosition(0, 0);
        int internalIndentation = 0;
        int internalLinefeeds = 0;
        if (prev.image != null) {
            int col = tok.beginColumn - 1;
            int lf = tok.beginLine - prev.endLine;
            if (lf <= 0)
                col -= prev.endColumn;
            position.setPosition(lf, col);
        }
        c.setRelativePosition(position);
        position.setPosition(tok.endLine, tok.endColumn);
        c.setEndPosition(position);
        position.setPosition(tok.beginLine, tok.beginColumn);
        c.setStartPosition(position);
        if (!(c instanceof recoder.java.DocComment)) {
            boolean hasEmptyLine = (c.getRelativePosition().getLine() > 1);
            c.setPrefixed(hasEmptyLine);
            if (tok.specialToken != null && !hasEmptyLine)
                c.setPrefixed(comments.get(comments.size() - 1).isPrefixed());
        }
        comments.add(c);
    }

    static void addSingleLineComment(Token tok) {
        addComment(factory.createSingleLineComment(tok.image.trim()), tok);
    }

    static void addMultiLineComment(Token tok) {
        addComment(factory.createComment(tok.image), tok);
    }

    static void addDocComment(Token tok) {
        addComment(factory.createDocComment(tok.image), tok);
    }

    public static List<Comment> getComments() {
        return comments;
    }

    public static final CompilationUnit CompilationUnit() throws ParseException {
        PackageSpecification ps = null;
        ASTArrayList aSTArrayList1 = new ASTArrayList();
        ASTArrayList aSTArrayList2 = new ASTArrayList();
        if (jj_2_1(2147483647)) {
            ps = PackageDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 39:
                        break;
                    default:
                        jj_la1[0] = jj_gen;
                        break;
                }
                Import imp = ImportDeclaration();
                aSTArrayList1.add(imp);
            }
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 13:
                    case 15:
                    case 22:
                    case 29:
                    case 32:
                    case 42:
                    case 48:
                    case 49:
                    case 50:
                    case 53:
                    case 67:
                    case 85:
                        break;
                    default:
                        jj_la1[1] = jj_gen;
                        break;
                }
                TypeDeclaration td = TypeDeclaration();
                if (td != null)
                    aSTArrayList2.add(td);
            }
        } else {
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 39:
                        break;
                    default:
                        jj_la1[2] = jj_gen;
                        break;
                }
                Import imp = ImportDeclaration();
                aSTArrayList1.add(imp);
            }
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 13:
                    case 15:
                    case 22:
                    case 29:
                    case 32:
                    case 42:
                    case 48:
                    case 49:
                    case 50:
                    case 53:
                    case 67:
                    case 85:
                        break;
                    default:
                        jj_la1[3] = jj_gen;
                        break;
                }
                TypeDeclaration td = TypeDeclaration();
                if (td != null)
                    aSTArrayList2.add(td);
            }
        }
        jj_consume_token(0);
        CompilationUnit result = factory.createCompilationUnit(ps, aSTArrayList1, aSTArrayList2);
        setPostfixInfo(result);
        setPrefixInfo(result);
        return result;
    }

    public static final PackageSpecification PackageDeclaration() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 15:
                    break;
                default:
                    jj_la1[4] = jj_gen;
                    break;
            }
            AnnotationUseSpecification annot = AnnotationUse();
            aSTArrayList.add(annot);
        }
        aSTArrayList.trimToSize();
        jj_consume_token(47);
        PackageSpecification result = factory.createPackageSpecification();
        setPrefixInfo(result);
        result.setAnnotations(aSTArrayList);
        UncollatedReferenceQualifier qn = Name();
        jj_consume_token(85);
        result.setPackageReference(qn.toPackageReference());
        setPostfixInfo(result);
        return result;
    }

    public static final Import ImportDeclaration() throws ParseException {
        String hs = null;
        boolean wildcard = false;
        boolean isStatic = false;
        jj_consume_token(39);
        Import result = factory.createImport();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 53:
                jj_consume_token(53);
                isStatic = true;
                break;
            default:
                jj_la1[5] = jj_gen;
                break;
        }
        UncollatedReferenceQualifier qn = Name();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 87:
                jj_consume_token(87);
                jj_consume_token(104);
                wildcard = true;
                break;
            default:
                jj_la1[6] = jj_gen;
                break;
        }
        jj_consume_token(85);
        result.setMultiImport(wildcard);
        if (isStatic) {
            result.setStaticImport(true);
            if (wildcard) {
                result.setReference(qn.toTypeReference());
            } else {
                result.setStaticIdentifier(qn.getIdentifier());
                UncollatedReferenceQualifier urq = (UncollatedReferenceQualifier) qn.getReferencePrefix();
                urq.setReferenceSuffix(null);
                result.setReference(urq.toTypeReference());
            }
        } else if (wildcard) {
            result.setReference(qn);
        } else {
            result.setReference(qn.toTypeReference());
        }
        setPostfixInfo(result);
        return result;
    }

    public static final TypeDeclaration TypeDeclaration() throws ParseException {
        AnnotationDeclaration annotationDeclaration;
        TypeDeclaration result = null;
        if (jj_2_2(2147483647)) {
            ClassDeclaration classDeclaration = ClassDeclaration();
        } else if (jj_2_3(2147483647)) {
            InterfaceDeclaration interfaceDeclaration = InterfaceDeclaration();
        } else if (jj_2_4(2147483647)) {
            EnumDeclaration enumDeclaration = EnumDeclaration();
        } else if (jj_2_5(2147483647)) {
            annotationDeclaration = AnnotationTypeDeclaration();
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 85:
                    jj_consume_token(85);
                    break;
                default:
                    jj_la1[7] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
        }
        if (annotationDeclaration != null)
            setPostfixInfo(annotationDeclaration);
        return annotationDeclaration;
    }

    public static final AnnotationDeclaration AnnotationTypeDeclaration() throws ParseException {
        ASTArrayList aSTArrayList1 = new ASTArrayList();
        ASTArrayList aSTArrayList2 = new ASTArrayList();
        AnnotationDeclaration result = new AnnotationDeclaration();
        while (jj_2_6(2)) {
            StrictFp strictFp;
            Public public_;
            Protected protected_;
            Private private_;
            Static static_;
            Abstract abstract_;
            AnnotationUseSpecification annotationUseSpecification;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 67:
                    jj_consume_token(67);
                    strictFp = factory.createStrictFp();
                    break;
                case 50:
                    jj_consume_token(50);
                    public_ = factory.createPublic();
                    break;
                case 49:
                    jj_consume_token(49);
                    protected_ = factory.createProtected();
                    break;
                case 48:
                    jj_consume_token(48);
                    private_ = factory.createPrivate();
                    break;
                case 53:
                    jj_consume_token(53);
                    static_ = factory.createStatic();
                    break;
                case 13:
                    jj_consume_token(13);
                    abstract_ = factory.createAbstract();
                    break;
                case 15:
                    annotationUseSpecification = AnnotationUse();
                    break;
                default:
                    jj_la1[8] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            aSTArrayList2.add(annotationUseSpecification);
        }
        jj_consume_token(15);
        setPrefixInfo(result);
        jj_consume_token(42);
        jj_consume_token(76);
        Identifier name = factory.createIdentifier(token.image);
        jj_consume_token(81);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                case 15:
                case 16:
                case 18:
                case 21:
                case 22:
                case 27:
                case 29:
                case 32:
                case 34:
                case 41:
                case 42:
                case 43:
                case 48:
                case 49:
                case 50:
                case 52:
                case 53:
                case 60:
                case 64:
                case 67:
                case 76:
                case 85:
                    break;
                default:
                    jj_la1[9] = jj_gen;
                    break;
            }
            if (jj_2_7(2147483647)) {
                ASTArrayList aSTArrayList = new ASTArrayList();
                while (true) {
                    AnnotationUseSpecification annotationUseSpecification;
                    Public public_;
                    Abstract abstract_;
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case 13:
                        case 15:
                        case 50:
                            break;
                        default:
                            jj_la1[10] = jj_gen;
                            break;
                    }
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case 15:
                            annotationUseSpecification = AnnotationUse();
                            break;
                        case 50:
                            jj_consume_token(50);
                            public_ = factory.createPublic();
                            break;
                        case 13:
                            jj_consume_token(13);
                            abstract_ = factory.createAbstract();
                            break;
                        default:
                            jj_la1[11] = jj_gen;
                            jj_consume_token(-1);
                            throw new ParseException();
                    }
                    aSTArrayList.add(abstract_);
                }
                TypeReference methodRes = Type();
                jj_consume_token(76);
                Identifier methodName = factory.createIdentifier(token.image);
                jj_consume_token(79);
                jj_consume_token(80);
                Expression methodDefExpr = null;
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 25:
                        jj_consume_token(25);
                        methodDefExpr = ElementValue();
                        break;
                    default:
                        jj_la1[12] = jj_gen;
                        break;
                }
                AnnotationPropertyDeclaration annotationPropertyDeclaration = factory.createAnnotationPropertyDeclaration(aSTArrayList, methodRes, methodName, methodDefExpr);
                aSTArrayList1.add(annotationPropertyDeclaration);
                continue;
            }
            if (jj_2_8(2147483647)) {
                FieldDeclaration fd = FieldDeclaration();
                aSTArrayList1.add(fd);
                continue;
            }
            if (jj_2_9(2147483647)) {
                ClassDeclaration classDeclaration = NestedClassDeclaration();
                aSTArrayList1.add(classDeclaration);
                continue;
            }
            if (jj_2_10(2147483647)) {
                EnumDeclaration enumDeclaration = EnumDeclaration();
                aSTArrayList1.add(enumDeclaration);
                continue;
            }
            if (jj_2_11(2147483647)) {
                InterfaceDeclaration interfaceDeclaration = NestedInterfaceDeclaration();
                aSTArrayList1.add(interfaceDeclaration);
                continue;
            }
            if (jj_2_12(2147483647)) {
                AnnotationDeclaration annotationDeclaration = AnnotationTypeDeclaration();
                aSTArrayList1.add(annotationDeclaration);
                continue;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 85:
                    jj_consume_token(85);
                    continue;
            }
            jj_la1[13] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        jj_consume_token(82);
        result.setDeclarationSpecifiers(aSTArrayList2);
        result.setIdentifier(name);
        result.setMembers(aSTArrayList1);
        setPostfixInfo(result);
        return result;
    }

    public static final EnumDeclaration EnumDeclaration() throws ParseException {
        Implements im;
        ASTList<UncollatedReferenceQualifier> nl;
        EnumConstantDeclaration constant;
        ASTArrayList aSTArrayList3;
        int i, s;
        ASTArrayList aSTArrayList1 = new ASTArrayList();
        ASTArrayList aSTArrayList2 = new ASTArrayList();
        while (jj_2_13(2)) {
            StrictFp strictFp;
            Public public_;
            Protected protected_;
            Private private_;
            Static static_;
            AnnotationUseSpecification annotationUseSpecification;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 67:
                    jj_consume_token(67);
                    strictFp = factory.createStrictFp();
                    break;
                case 50:
                    jj_consume_token(50);
                    public_ = factory.createPublic();
                    break;
                case 49:
                    jj_consume_token(49);
                    protected_ = factory.createProtected();
                    break;
                case 48:
                    jj_consume_token(48);
                    private_ = factory.createPrivate();
                    break;
                case 53:
                    jj_consume_token(53);
                    static_ = factory.createStatic();
                    break;
                case 15:
                    annotationUseSpecification = AnnotationUse();
                    break;
                default:
                    jj_la1[14] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            setPrefixInfo(annotationUseSpecification);
            setPostfixInfo(annotationUseSpecification);
            aSTArrayList1.add(annotationUseSpecification);
        }
        jj_consume_token(29);
        EnumDeclaration result = new EnumDeclaration();
        setPrefixInfo(result);
        if (aSTArrayList1.size() != 0)
            result.setDeclarationSpecifiers(aSTArrayList1);
        jj_consume_token(76);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        result.setIdentifier(id);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 38:
                jj_consume_token(38);
                im = factory.createImplements();
                setPrefixInfo(im);
                nl = TypedNameList();
                aSTArrayList3 = new ASTArrayList();
                for (i = 0, s = nl.size(); i < s; i++) {
                    TypeReference tr = nl.get(i).toTypeReference();
                    aSTArrayList3.add(tr);
                }
                im.setSupertypes(aSTArrayList3);
                result.setImplementedTypes(im);
                break;
            default:
                jj_la1[15] = jj_gen;
                break;
        }
        jj_consume_token(81);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 15:
            case 76:
                constant = EnumConstant();
                aSTArrayList2.add(constant);
                while (jj_2_14(2)) {
                    jj_consume_token(86);
                    constant = EnumConstant();
                    aSTArrayList2.add(constant);
                }
                break;
            default:
                jj_la1[16] = jj_gen;
                break;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 86:
                jj_consume_token(86);
                break;
            default:
                jj_la1[17] = jj_gen;
                break;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 85:
                jj_consume_token(85);
                while (true) {
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case 13:
                        case 15:
                        case 16:
                        case 18:
                        case 21:
                        case 22:
                        case 27:
                        case 29:
                        case 32:
                        case 34:
                        case 41:
                        case 42:
                        case 43:
                        case 44:
                        case 48:
                        case 49:
                        case 50:
                        case 52:
                        case 53:
                        case 56:
                        case 60:
                        case 63:
                        case 64:
                        case 67:
                        case 76:
                        case 81:
                        case 89:
                            break;
                        default:
                            jj_la1[18] = jj_gen;
                            break;
                    }
                    MemberDeclaration md = ClassBodyDeclaration();
                    aSTArrayList2.add(md);
                }
                jj_consume_token(82);
                result.setMembers(aSTArrayList2);
                setPostfixInfo(result);
                return result;
        }
        jj_la1[19] = jj_gen;
        jj_consume_token(82);
        result.setMembers(aSTArrayList2);
        setPostfixInfo(result);
        return result;
    }

    public static final EnumConstantDeclaration EnumConstant() throws ParseException {
        ASTArrayList<DeclarationSpecifier> annotations = null;
        ASTList<Expression> args = null;
        ClassDeclaration cd = null;
        ASTList<MemberDeclaration> body = null;
        EnumConstructorReference ref = null;
        EnumConstantDeclaration result = new EnumConstantDeclaration();
        setPrefixInfo(result);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 15:
                    break;
                default:
                    jj_la1[20] = jj_gen;
                    break;
            }
            if (annotations == null)
                annotations = new ASTArrayList();
            AnnotationUseSpecification annot = AnnotationUse();
            annotations.add(annot);
        }
        jj_consume_token(76);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 79:
                args = Arguments();
                break;
            default:
                jj_la1[21] = jj_gen;
                break;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 81:
                cd = factory.createClassDeclaration();
                setPrefixInfo(cd);
                body = ClassBody();
                cd.setMembers(body);
                setPostfixInfo(cd);
                ref = new EnumConstructorReference(args, cd);
                setPrefixInfo(ref);
                setPostfixInfo(ref);
                spec = new EnumConstantSpecification(id, ref);
                setPrefixInfo((SourceElement) spec);
                setPostfixInfo((SourceElement) spec);
                setPostfixInfo(result);
                result.setEnumConstantSpecification(spec);
                result.setDeclarationSpecifiers(annotations);
                return result;
        }
        jj_la1[22] = jj_gen;
        ref = new EnumConstructorReference(args, cd);
        setPrefixInfo(ref);
        setPostfixInfo(ref);
        EnumConstantSpecification spec = new EnumConstantSpecification(id, ref);
        setPrefixInfo(spec);
        setPostfixInfo(spec);
        setPostfixInfo(result);
        result.setEnumConstantSpecification(spec);
        result.setDeclarationSpecifiers(annotations);
        return result;
    }

    public static final ClassDeclaration ClassDeclaration() throws ParseException {
        ClassDeclaration result = null;
        ASTArrayList aSTArrayList = new ASTArrayList();
        while (true) {
            Abstract abstract_;
            Final final_;
            Public public_;
            StrictFp strictFp;
            AnnotationUseSpecification annotationUseSpecification;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                case 15:
                case 32:
                case 50:
                case 67:
                    break;
                default:
                    jj_la1[23] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                    jj_consume_token(13);
                    abstract_ = factory.createAbstract();
                    break;
                case 32:
                    jj_consume_token(32);
                    final_ = factory.createFinal();
                    break;
                case 50:
                    jj_consume_token(50);
                    public_ = factory.createPublic();
                    break;
                case 67:
                    jj_consume_token(67);
                    strictFp = factory.createStrictFp();
                    break;
                case 15:
                    annotationUseSpecification = AnnotationUse();
                    break;
                default:
                    jj_la1[24] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            setPrefixInfo(annotationUseSpecification);
            setPostfixInfo(annotationUseSpecification);
            aSTArrayList.add(annotationUseSpecification);
        }
        result = UnmodifiedClassDeclaration();
        result.setDeclarationSpecifiers(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final ClassDeclaration UnmodifiedClassDeclaration() throws ParseException {
        UncollatedReferenceQualifier qn;
        ASTList<UncollatedReferenceQualifier> nl;
        Extends ex;
        Implements im;
        ASTArrayList aSTArrayList;
        int i, s;
        ASTList<TypeParameterDeclaration> typeParams = null;
        jj_consume_token(22);
        ClassDeclaration result = factory.createClassDeclaration();
        setPrefixInfo(result);
        jj_consume_token(76);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        result.setIdentifier(id);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 89:
                typeParams = TypeParameters();
                result.setTypeParameters(typeParams);
                break;
            default:
                jj_la1[25] = jj_gen;
                break;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 30:
                jj_consume_token(30);
                ex = factory.createExtends();
                setPrefixInfo(ex);
                qn = TypedName();
                ex.setSupertypes(new ASTArrayList(1));
                ex.getSupertypes().add(qn.toTypeReference());
                result.setExtendedTypes(ex);
                break;
            default:
                jj_la1[26] = jj_gen;
                break;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 38:
                jj_consume_token(38);
                im = factory.createImplements();
                setPrefixInfo(im);
                nl = TypedNameList();
                aSTArrayList = new ASTArrayList();
                for (i = 0, s = nl.size(); i < s; i++) {
                    TypeReference tr = nl.get(i).toTypeReference();
                    aSTArrayList.add(tr);
                }
                im.setSupertypes(aSTArrayList);
                result.setImplementedTypes(im);
                mdl = ClassBody();
                result.setMembers(mdl);
                setPostfixInfo(result);
                return result;
        }
        jj_la1[27] = jj_gen;
        ASTList<MemberDeclaration> mdl = ClassBody();
        result.setMembers(mdl);
        setPostfixInfo(result);
        return result;
    }

    public static final ASTList<MemberDeclaration> ClassBody() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        jj_consume_token(81);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                case 15:
                case 16:
                case 18:
                case 21:
                case 22:
                case 27:
                case 29:
                case 32:
                case 34:
                case 41:
                case 42:
                case 43:
                case 44:
                case 48:
                case 49:
                case 50:
                case 52:
                case 53:
                case 56:
                case 60:
                case 63:
                case 64:
                case 67:
                case 76:
                case 81:
                case 89:
                    break;
                default:
                    jj_la1[28] = jj_gen;
                    break;
            }
            MemberDeclaration md = ClassBodyDeclaration();
            aSTArrayList.add(md);
        }
        jj_consume_token(82);
        return (ASTList<MemberDeclaration>) aSTArrayList;
    }

    public static final ClassDeclaration NestedClassDeclaration() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        while (true) {
            Static static_;
            Abstract abstract_;
            Final final_;
            Public public_;
            Protected protected_;
            Private private_;
            StrictFp strictFp;
            AnnotationUseSpecification annotationUseSpecification;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                case 15:
                case 32:
                case 48:
                case 49:
                case 50:
                case 53:
                case 67:
                    break;
                default:
                    jj_la1[29] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 53:
                    jj_consume_token(53);
                    static_ = factory.createStatic();
                    break;
                case 13:
                    jj_consume_token(13);
                    abstract_ = factory.createAbstract();
                    break;
                case 32:
                    jj_consume_token(32);
                    final_ = factory.createFinal();
                    break;
                case 50:
                    jj_consume_token(50);
                    public_ = factory.createPublic();
                    break;
                case 49:
                    jj_consume_token(49);
                    protected_ = factory.createProtected();
                    break;
                case 48:
                    jj_consume_token(48);
                    private_ = factory.createPrivate();
                    break;
                case 67:
                    jj_consume_token(67);
                    strictFp = factory.createStrictFp();
                    break;
                case 15:
                    annotationUseSpecification = AnnotationUse();
                    break;
                default:
                    jj_la1[30] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            setPrefixInfo(annotationUseSpecification);
            setPostfixInfo(annotationUseSpecification);
            aSTArrayList.add(annotationUseSpecification);
        }
        ClassDeclaration result = UnmodifiedClassDeclaration();
        result.setDeclarationSpecifiers(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final MemberDeclaration ClassBodyDeclaration() throws ParseException {
        FieldDeclaration fieldDeclaration;
        if (jj_2_15(2)) {
            ClassInitializer classInitializer = Initializer();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[31] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else if (jj_2_16(2147483647)) {
            ClassDeclaration classDeclaration = NestedClassDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[32] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else if (jj_2_17(2147483647)) {
            InterfaceDeclaration interfaceDeclaration = NestedInterfaceDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[33] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else if (jj_2_18(2147483647)) {
            ConstructorDeclaration constructorDeclaration = ConstructorDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[34] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else if (jj_2_19(2147483647)) {
            MethodDeclaration methodDeclaration = MethodDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[35] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else if (jj_2_20(2147483647)) {
            EnumDeclaration enumDeclaration = EnumDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[36] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else if (jj_2_21(2147483647)) {
            AnnotationDeclaration annotationDeclaration = AnnotationTypeDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[37] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 15:
                case 16:
                case 18:
                case 21:
                case 27:
                case 32:
                case 34:
                case 41:
                case 43:
                case 48:
                case 49:
                case 50:
                case 52:
                case 53:
                case 60:
                case 64:
                case 76:
                    fieldDeclaration = FieldDeclaration();
                    while (true) {
                        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                            case 85:
                                break;
                            default:
                                jj_la1[38] = jj_gen;
                                break;
                        }
                        jj_consume_token(85);
                    }
                    setPostfixInfo(fieldDeclaration);
                    return fieldDeclaration;
            }
            jj_la1[39] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(fieldDeclaration);
        return fieldDeclaration;
    }

    public static final InterfaceDeclaration InterfaceDeclaration() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        while (true) {
            Abstract abstract_;
            Public public_;
            StrictFp strictFp;
            AnnotationUseSpecification annotationUseSpecification;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                case 15:
                case 50:
                case 67:
                    break;
                default:
                    jj_la1[40] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                    jj_consume_token(13);
                    abstract_ = factory.createAbstract();
                    break;
                case 50:
                    jj_consume_token(50);
                    public_ = factory.createPublic();
                    break;
                case 67:
                    jj_consume_token(67);
                    strictFp = factory.createStrictFp();
                    break;
                case 15:
                    annotationUseSpecification = AnnotationUse();
                    break;
                default:
                    jj_la1[41] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            setPrefixInfo(annotationUseSpecification);
            setPostfixInfo(annotationUseSpecification);
            aSTArrayList.add(annotationUseSpecification);
        }
        InterfaceDeclaration result = UnmodifiedInterfaceDeclaration();
        result.setDeclarationSpecifiers(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final InterfaceDeclaration NestedInterfaceDeclaration() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        while (true) {
            Static static_;
            Abstract abstract_;
            Final final_;
            Public public_;
            Protected protected_;
            Private private_;
            StrictFp strictFp;
            AnnotationUseSpecification annotationUseSpecification;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                case 15:
                case 32:
                case 48:
                case 49:
                case 50:
                case 53:
                case 67:
                    break;
                default:
                    jj_la1[42] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 53:
                    jj_consume_token(53);
                    static_ = factory.createStatic();
                    break;
                case 13:
                    jj_consume_token(13);
                    abstract_ = factory.createAbstract();
                    break;
                case 32:
                    jj_consume_token(32);
                    final_ = factory.createFinal();
                    break;
                case 50:
                    jj_consume_token(50);
                    public_ = factory.createPublic();
                    break;
                case 49:
                    jj_consume_token(49);
                    protected_ = factory.createProtected();
                    break;
                case 48:
                    jj_consume_token(48);
                    private_ = factory.createPrivate();
                    break;
                case 67:
                    jj_consume_token(67);
                    strictFp = factory.createStrictFp();
                    break;
                case 15:
                    annotationUseSpecification = AnnotationUse();
                    break;
                default:
                    jj_la1[43] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            setPrefixInfo(annotationUseSpecification);
            setPostfixInfo(annotationUseSpecification);
            aSTArrayList.add(annotationUseSpecification);
        }
        InterfaceDeclaration result = UnmodifiedInterfaceDeclaration();
        result.setDeclarationSpecifiers(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final InterfaceDeclaration UnmodifiedInterfaceDeclaration() throws ParseException {
        ASTList<UncollatedReferenceQualifier> nl;
        Extends ex;
        ASTArrayList aSTArrayList2;
        int i, s;
        ASTArrayList aSTArrayList1 = new ASTArrayList();
        ASTList<TypeParameterDeclaration> typeParams = null;
        jj_consume_token(42);
        InterfaceDeclaration result = factory.createInterfaceDeclaration();
        setPrefixInfo(result);
        jj_consume_token(76);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        result.setIdentifier(id);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 89:
                typeParams = TypeParameters();
                result.setTypeParameters(typeParams);
                break;
            default:
                jj_la1[44] = jj_gen;
                break;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 30:
                jj_consume_token(30);
                ex = factory.createExtends();
                setPrefixInfo(ex);
                nl = TypedNameList();
                aSTArrayList2 = new ASTArrayList();
                for (i = 0, s = nl.size(); i < s; i++) {
                    TypeReference tr = nl.get(i).toTypeReference();
                    aSTArrayList2.add(tr);
                }
                ex.setSupertypes(aSTArrayList2);
                result.setExtendedTypes(ex);
                break;
            default:
                jj_la1[45] = jj_gen;
                break;
        }
        jj_consume_token(81);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                case 15:
                case 16:
                case 18:
                case 21:
                case 22:
                case 27:
                case 29:
                case 32:
                case 34:
                case 41:
                case 42:
                case 43:
                case 44:
                case 48:
                case 49:
                case 50:
                case 52:
                case 53:
                case 56:
                case 60:
                case 63:
                case 64:
                case 67:
                case 76:
                case 89:
                    break;
                default:
                    jj_la1[46] = jj_gen;
                    break;
            }
            MemberDeclaration md = InterfaceMemberDeclaration();
            aSTArrayList1.add(md);
        }
        jj_consume_token(82);
        result.setMembers(aSTArrayList1);
        setPostfixInfo(result);
        return result;
    }

    public static final MemberDeclaration InterfaceMemberDeclaration() throws ParseException {
        FieldDeclaration fieldDeclaration;
        if (jj_2_22(2147483647)) {
            ClassDeclaration classDeclaration = NestedClassDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[47] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else if (jj_2_23(2147483647)) {
            InterfaceDeclaration interfaceDeclaration = NestedInterfaceDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[48] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else if (jj_2_24(2147483647)) {
            MethodDeclaration methodDeclaration = MethodDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[49] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else if (jj_2_25(2147483647)) {
            EnumDeclaration enumDeclaration = EnumDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[50] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else if (jj_2_26(2147483647)) {
            AnnotationDeclaration annotationDeclaration = AnnotationTypeDeclaration();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 85:
                        break;
                    default:
                        jj_la1[51] = jj_gen;
                        break;
                }
                jj_consume_token(85);
            }
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 15:
                case 16:
                case 18:
                case 21:
                case 27:
                case 32:
                case 34:
                case 41:
                case 43:
                case 48:
                case 49:
                case 50:
                case 52:
                case 53:
                case 60:
                case 64:
                case 76:
                    fieldDeclaration = FieldDeclaration();
                    while (true) {
                        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                            case 85:
                                break;
                            default:
                                jj_la1[52] = jj_gen;
                                break;
                        }
                        jj_consume_token(85);
                    }
                    setPostfixInfo(fieldDeclaration);
                    return fieldDeclaration;
            }
            jj_la1[53] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(fieldDeclaration);
        return fieldDeclaration;
    }

    public static final FieldDeclaration FieldDeclaration() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        DeclarationSpecifier m = null;
        ASTArrayList<FieldSpecification> vl = new ASTArrayList();
        boolean hasPrefixInfo = false;
        FieldDeclaration result = factory.createFieldDeclaration();
        while (true) {
            Public public_;
            Protected protected_;
            Private private_;
            Static static_;
            Final final_;
            Transient transient_;
            Volatile volatile_;
            AnnotationUseSpecification annotationUseSpecification;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 15:
                case 32:
                case 48:
                case 49:
                case 50:
                case 53:
                case 60:
                case 64:
                    break;
                default:
                    jj_la1[54] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 50:
                    jj_consume_token(50);
                    public_ = factory.createPublic();
                    break;
                case 49:
                    jj_consume_token(49);
                    protected_ = factory.createProtected();
                    break;
                case 48:
                    jj_consume_token(48);
                    private_ = factory.createPrivate();
                    break;
                case 53:
                    jj_consume_token(53);
                    static_ = factory.createStatic();
                    break;
                case 32:
                    jj_consume_token(32);
                    final_ = factory.createFinal();
                    break;
                case 60:
                    jj_consume_token(60);
                    transient_ = factory.createTransient();
                    break;
                case 64:
                    jj_consume_token(64);
                    volatile_ = factory.createVolatile();
                    break;
                case 15:
                    annotationUseSpecification = AnnotationUse();
                    break;
                default:
                    jj_la1[55] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            setPrefixInfo(annotationUseSpecification);
            setPostfixInfo(annotationUseSpecification);
            aSTArrayList.add(annotationUseSpecification);
            if (!hasPrefixInfo) {
                copyPrefixInfo(annotationUseSpecification, result);
                hasPrefixInfo = true;
            }
        }
        TypeReference tr = Type();
        if (!hasPrefixInfo)
            copyPrefixInfo(tr, result);
        result.setDeclarationSpecifiers(aSTArrayList);
        result.setTypeReference(tr);
        VariableSpecification var = VariableDeclarator(true);
        vl.add(var);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 86:
                    break;
                default:
                    jj_la1[56] = jj_gen;
                    break;
            }
            jj_consume_token(86);
            var = VariableDeclarator(true);
            vl.add(var);
        }
        jj_consume_token(85);
        result.setFieldSpecifications(vl);
        setPostfixInfo(result);
        return result;
    }

    public static final VariableSpecification VariableDeclarator(boolean isForField) throws ParseException {
        VariableSpecification result;
        int dim = 0;
        Expression init = null;
        Identifier id = VariableDeclaratorId();
        dim = tmpDimension;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 88:
                jj_consume_token(88);
                init = VariableInitializer();
                break;
            default:
                jj_la1[57] = jj_gen;
                break;
        }
        if (isForField) {
            FieldSpecification fieldSpecification = factory.createFieldSpecification(id, dim, init);
        } else {
            result = factory.createVariableSpecification(id, dim, init);
        }
        setPostfixInfo(result);
        return result;
    }

    public static final Identifier VariableDeclaratorId() throws ParseException {
        jj_consume_token(76);
        Identifier result = factory.createIdentifier(token.image);
        setPrefixInfo(result);
        setPostfixInfo(result);
        tmpDimension = 0;
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 83:
                    break;
                default:
                    jj_la1[58] = jj_gen;
                    break;
            }
            jj_consume_token(83);
            jj_consume_token(84);
            tmpDimension++;
        }
        setPostfixInfo(result);
        return result;
    }

    public static final Expression VariableInitializer() throws ParseException {
        ArrayInitializer arrayInitializer;
        Expression expression;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 81:
                arrayInitializer = ArrayInitializer();
                setPostfixInfo(arrayInitializer);
                return arrayInitializer;
            case 16:
            case 18:
            case 21:
            case 27:
            case 31:
            case 34:
            case 41:
            case 43:
            case 45:
            case 46:
            case 52:
            case 54:
            case 57:
            case 61:
            case 63:
            case 68:
            case 72:
            case 74:
            case 75:
            case 76:
            case 79:
            case 90:
            case 91:
            case 100:
            case 101:
            case 102:
            case 103:
                expression = Expression();
                setPostfixInfo(expression);
                return expression;
        }
        jj_la1[59] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final ArrayInitializer ArrayInitializer() throws ParseException {
        Expression init;
        ASTArrayList aSTArrayList = new ASTArrayList();
        jj_consume_token(81);
        ArrayInitializer result = factory.createArrayInitializer();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 16:
            case 18:
            case 21:
            case 27:
            case 31:
            case 34:
            case 41:
            case 43:
            case 45:
            case 46:
            case 52:
            case 54:
            case 57:
            case 61:
            case 63:
            case 68:
            case 72:
            case 74:
            case 75:
            case 76:
            case 79:
            case 81:
            case 90:
            case 91:
            case 100:
            case 101:
            case 102:
            case 103:
                init = VariableInitializer();
                aSTArrayList.add(init);
                while (jj_2_27(2)) {
                    jj_consume_token(86);
                    init = VariableInitializer();
                    aSTArrayList.add(init);
                }
                break;
            default:
                jj_la1[60] = jj_gen;
                break;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 86:
                jj_consume_token(86);
                jj_consume_token(82);
                result.setArguments(aSTArrayList);
                setPostfixInfo(result);
                return result;
        }
        jj_la1[61] = jj_gen;
        jj_consume_token(82);
        result.setArguments(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final MethodDeclaration MethodDeclaration() throws ParseException {
        Public public_;
        ASTArrayList aSTArrayList = new ASTArrayList();
        DeclarationSpecifier m = null;
        ASTList<UncollatedReferenceQualifier> nl = null;
        Throws th = null;
        StatementBlock body = null;
        ASTList<TypeParameterDeclaration> typeParams = null;
        SourceElement dummy = null;
        while (true) {
            Public public_1;
            Protected protected_;
            Private private_;
            Static static_;
            Final final_;
            Abstract abstract_;
            Native native_;
            Synchronized synchronized_;
            StrictFp strictFp;
            AnnotationUseSpecification annotationUseSpecification;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                case 15:
                case 32:
                case 44:
                case 48:
                case 49:
                case 50:
                case 53:
                case 56:
                case 67:
                    break;
                default:
                    jj_la1[62] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 50:
                    jj_consume_token(50);
                    public_1 = factory.createPublic();
                    break;
                case 49:
                    jj_consume_token(49);
                    protected_ = factory.createProtected();
                    break;
                case 48:
                    jj_consume_token(48);
                    private_ = factory.createPrivate();
                    break;
                case 53:
                    jj_consume_token(53);
                    static_ = factory.createStatic();
                    break;
                case 32:
                    jj_consume_token(32);
                    final_ = factory.createFinal();
                    break;
                case 13:
                    jj_consume_token(13);
                    abstract_ = factory.createAbstract();
                    break;
                case 44:
                    jj_consume_token(44);
                    native_ = factory.createNative();
                    break;
                case 56:
                    jj_consume_token(56);
                    synchronized_ = factory.createSynchronized();
                    break;
                case 67:
                    jj_consume_token(67);
                    strictFp = factory.createStrictFp();
                    break;
                case 15:
                    annotationUseSpecification = AnnotationUse();
                    break;
                default:
                    jj_la1[63] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            setPrefixInfo(annotationUseSpecification);
            setPostfixInfo(annotationUseSpecification);
            aSTArrayList.add(annotationUseSpecification);
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 89:
                jj_consume_token(89);
                if (aSTArrayList.size() == 0) {
                    public_ = factory.createPublic();
                    setPrefixInfo(public_);
                }
                typeParams = TypeParametersNoLE();
                break;
            default:
                jj_la1[64] = jj_gen;
                break;
        }
        TypeReference tr = ResultType();
        MethodDeclaration result = MethodDeclarator(tr);
        if (public_ != null) {
            copyPrefixInfo(public_, result);
            public_ = null;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 59:
                jj_consume_token(59);
                th = factory.createThrows();
                setPrefixInfo(th);
                nl = TypedNameList();
                break;
            default:
                jj_la1[65] = jj_gen;
                break;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 81:
                body = Block();
                break;
            case 85:
                jj_consume_token(85);
                break;
            default:
                jj_la1[66] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
        }
        if (nl != null) {
            ASTArrayList aSTArrayList1 = new ASTArrayList();
            for (int i = 0, s = nl.size(); i < s; i++)
                aSTArrayList1.add(nl.get(i).toTypeReference());
            th.setExceptions(aSTArrayList1);
            result.setThrown(th);
        }
        result.setTypeParameters(typeParams);
        result.setDeclarationSpecifiers(aSTArrayList);
        result.setBody(body);
        setPostfixInfo(result);
        return result;
    }

    public static final void MethodDeclarationLookahead() throws ParseException {
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 13:
                case 15:
                case 32:
                case 44:
                case 48:
                case 49:
                case 50:
                case 53:
                case 56:
                case 67:
                    break;
                default:
                    jj_la1[67] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 50:
                    jj_consume_token(50);
                    continue;
                case 49:
                    jj_consume_token(49);
                    continue;
                case 48:
                    jj_consume_token(48);
                    continue;
                case 53:
                    jj_consume_token(53);
                    continue;
                case 13:
                    jj_consume_token(13);
                    continue;
                case 32:
                    jj_consume_token(32);
                    continue;
                case 44:
                    jj_consume_token(44);
                    continue;
                case 56:
                    jj_consume_token(56);
                    continue;
                case 67:
                    jj_consume_token(67);
                    continue;
                case 15:
                    AnnotationUse();
                    continue;
            }
            jj_la1[68] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 89:
                TypeParameters();
                break;
            default:
                jj_la1[69] = jj_gen;
                break;
        }
        ResultType();
        jj_consume_token(76);
        jj_consume_token(79);
    }

    public static final MethodDeclaration MethodDeclarator(TypeReference tr) throws ParseException {
        jj_consume_token(76);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        ASTList<ParameterDeclaration> pdl = FormalParameters();
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 83:
                    break;
                default:
                    jj_la1[70] = jj_gen;
                    break;
            }
            jj_consume_token(83);
            jj_consume_token(84);
            if (tr != null)
                tr.setDimensions(tr.getDimensions() + 1);
        }
        MethodDeclaration result = factory.createMethodDeclaration();
        result.setIdentifier(id);
        result.setTypeReference(tr);
        result.setParameters(pdl);
        setPrefixInfo(result);
        setPostfixInfo(result);
        return result;
    }

    public static final ASTList<ParameterDeclaration> FormalParameters() throws ParseException {
        ParameterDeclaration pd;
        ASTArrayList aSTArrayList = new ASTArrayList();
        jj_consume_token(79);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 15:
            case 16:
            case 18:
            case 21:
            case 27:
            case 32:
            case 34:
            case 41:
            case 43:
            case 52:
            case 76:
                pd = FormalParameter();
                aSTArrayList.add(pd);
                while (true) {
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case 86:
                            break;
                        default:
                            jj_la1[71] = jj_gen;
                            break;
                    }
                    jj_consume_token(86);
                    pd = FormalParameter();
                    aSTArrayList.add(pd);
                }
                jj_consume_token(80);
                return (ASTList<ParameterDeclaration>) aSTArrayList;
        }
        jj_la1[72] = jj_gen;
        jj_consume_token(80);
        return (ASTList<ParameterDeclaration>) aSTArrayList;
    }

    public static final ParameterDeclaration FormalParameter() throws ParseException {
        Final final_;
        ASTArrayList aSTArrayList;
        DeclarationSpecifier mod = null;
        ASTList<DeclarationSpecifier> ml = null;
        boolean isVarArg = false;
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 15:
                    break;
                default:
                    jj_la1[73] = jj_gen;
                    break;
            }
            AnnotationUseSpecification annotationUseSpecification = AnnotationUse();
            if (ml == null)
                aSTArrayList = new ASTArrayList();
            setPrefixInfo(annotationUseSpecification);
            setPostfixInfo(annotationUseSpecification);
            aSTArrayList.add(annotationUseSpecification);
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 32:
                jj_consume_token(32);
                final_ = factory.createFinal();
                setPrefixInfo(final_);
                setPostfixInfo(final_);
                if (aSTArrayList == null)
                    aSTArrayList = new ASTArrayList();
                aSTArrayList.add(final_);
                while (true) {
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case 15:
                            break;
                        default:
                            jj_la1[74] = jj_gen;
                            break;
                    }
                    AnnotationUseSpecification annotationUseSpecification = AnnotationUse();
                    setPrefixInfo(annotationUseSpecification);
                    setPostfixInfo(annotationUseSpecification);
                    aSTArrayList.add(annotationUseSpecification);
                }
                break;
            default:
                jj_la1[75] = jj_gen;
                break;
        }
        TypeReference tr = Type();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 66:
                jj_consume_token(66);
                isVarArg = true;
                break;
            default:
                jj_la1[76] = jj_gen;
                break;
        }
        Identifier id = VariableDeclaratorId();
        int dim = tmpDimension;
        ParameterDeclaration result = factory.createParameterDeclaration(tr, id);
        if (aSTArrayList != null)
            result.setDeclarationSpecifiers(aSTArrayList);
        VariableSpecification vspec = result.getVariables().get(0);
        vspec.setDimensions(dim);
        setPostfixInfo(result);
        setPrefixInfo(result);
        result.setVarArg(isVarArg);
        return result;
    }

    public static final ConstructorDeclaration ConstructorDeclaration() throws ParseException {
        Public public_;
        Protected protected_;
        Private private_;
        DeclarationSpecifier m = null;
        ASTArrayList aSTArrayList1 = new ASTArrayList();
        ASTList<UncollatedReferenceQualifier> nl = null;
        SpecialConstructorReference scr = null;
        ASTArrayList aSTArrayList2 = new ASTArrayList();
        ConstructorDeclaration result = factory.createConstructorDeclaration();
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 15:
                    break;
                default:
                    jj_la1[77] = jj_gen;
                    break;
            }
            AnnotationUseSpecification annotationUseSpecification = AnnotationUse();
            setPrefixInfo(annotationUseSpecification);
            setPostfixInfo(annotationUseSpecification);
            aSTArrayList1.add(annotationUseSpecification);
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 48:
            case 49:
            case 50:
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 50:
                        jj_consume_token(50);
                        public_ = factory.createPublic();
                        break;
                    case 49:
                        jj_consume_token(49);
                        protected_ = factory.createProtected();
                        break;
                    case 48:
                        jj_consume_token(48);
                        private_ = factory.createPrivate();
                        break;
                    default:
                        jj_la1[78] = jj_gen;
                        jj_consume_token(-1);
                        throw new ParseException();
                }
                setPrefixInfo(private_);
                setPostfixInfo(private_);
                aSTArrayList1.add(private_);
                while (true) {
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case 15:
                            break;
                        default:
                            jj_la1[79] = jj_gen;
                            break;
                    }
                    AnnotationUseSpecification annotationUseSpecification = AnnotationUse();
                    setPrefixInfo(annotationUseSpecification);
                    setPostfixInfo(annotationUseSpecification);
                    aSTArrayList1.add(annotationUseSpecification);
                }
                break;
            default:
                jj_la1[80] = jj_gen;
                break;
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 89:
                TypeParameters();
                break;
            default:
                jj_la1[81] = jj_gen;
                break;
        }
        jj_consume_token(76);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        ASTList<ParameterDeclaration> pdl = FormalParameters();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 59:
                jj_consume_token(59);
                nl = TypedNameList();
                break;
            default:
                jj_la1[82] = jj_gen;
                break;
        }
        jj_consume_token(81);
        StatementBlock body = factory.createStatementBlock();
        setPrefixInfo(body);
        body.setBody(aSTArrayList2);
        setAllowSuper(false);
        if (jj_2_28(2147483647)) {
            scr = ExplicitConstructorInvocation();
            aSTArrayList2.add(scr);
        }
        setAllowSuper(true);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 14:
                case 15:
                case 16:
                case 17:
                case 18:
                case 21:
                case 22:
                case 24:
                case 26:
                case 27:
                case 31:
                case 32:
                case 34:
                case 35:
                case 37:
                case 41:
                case 43:
                case 45:
                case 46:
                case 51:
                case 52:
                case 54:
                case 55:
                case 56:
                case 57:
                case 58:
                case 61:
                case 62:
                case 63:
                case 65:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                case 81:
                case 85:
                case 100:
                case 101:
                    break;
                default:
                    jj_la1[83] = jj_gen;
                    break;
            }
            Statement stat = BlockStatement();
            aSTArrayList2.add(stat);
        }
        jj_consume_token(82);
        setPostfixInfo(body);
        result.setIdentifier(id);
        result.setParameters(pdl);
        if (!aSTArrayList1.isEmpty())
            result.setDeclarationSpecifiers(aSTArrayList1);
        if (nl != null) {
            int s = nl.size();
            ASTArrayList aSTArrayList = new ASTArrayList(s);
            for (int i = 0; i < s; i++)
                aSTArrayList.add(nl.get(i).toTypeReference());
            Throws th = factory.createThrows(aSTArrayList);
            setPrefixInfo(th);
            result.setThrown(th);
        }
        result.setBody(body);
        setPostfixInfo(result);
        return result;
    }

    public static final SpecialConstructorReference ExplicitConstructorInvocation() throws ParseException {
        SuperConstructorReference superConstructorReference;
        Expression expr = null;
        if (jj_2_30(2147483647)) {
            jj_consume_token(57);
            ThisConstructorReference thisConstructorReference = factory.createThisConstructorReference();
            setPrefixInfo(thisConstructorReference);
            ASTList<Expression> args = Arguments();
            jj_consume_token(85);
            thisConstructorReference.setArguments(args);
        } else {
            ASTList<Expression> args;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 16:
                case 18:
                case 21:
                case 27:
                case 31:
                case 34:
                case 41:
                case 43:
                case 45:
                case 46:
                case 52:
                case 54:
                case 57:
                case 61:
                case 63:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                    if (jj_2_29(2)) {
                        expr = PrimaryExpression();
                        jj_consume_token(87);
                    }
                    jj_consume_token(54);
                    superConstructorReference = factory.createSuperConstructorReference();
                    setPrefixInfo(superConstructorReference);
                    args = Arguments();
                    jj_consume_token(85);
                    superConstructorReference.setArguments(args);
                    superConstructorReference.setReferencePrefix((ReferencePrefix) expr);
                    setPostfixInfo(superConstructorReference);
                    return superConstructorReference;
            }
            jj_la1[84] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(superConstructorReference);
        return superConstructorReference;
    }

    public static final ClassInitializer Initializer() throws ParseException {
        ASTArrayList aSTArrayList;
        Static s;
        ASTList<DeclarationSpecifier> ml = null;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 53:
                jj_consume_token(53);
                aSTArrayList = new ASTArrayList();
                s = factory.createStatic();
                setPrefixInfo(s);
                setPostfixInfo(s);
                aSTArrayList.add(s);
                break;
            default:
                jj_la1[85] = jj_gen;
                break;
        }
        StatementBlock block = Block();
        ClassInitializer result = factory.createClassInitializer(block);
        setPrefixInfo(result);
        if (aSTArrayList != null)
            result.setDeclarationSpecifiers(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final TypeReference Type() throws ParseException {
        TypeReference result;
        int dimension = 0;
        if (jj_2_31(2147483647)) {
            UncollatedReferenceQualifier qn = TypedName();
            result = qn.toTypeReference();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 83:
                        break;
                    default:
                        jj_la1[86] = jj_gen;
                        break;
                }
                jj_consume_token(83);
                jj_consume_token(84);
                if (dimension == 0)
                    setPrefixInfo(result);
                dimension++;
            }
            result.setDimensions(dimension);
            setPostfixInfo(result);
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 16:
                case 18:
                case 21:
                case 27:
                case 34:
                case 41:
                case 43:
                case 52:
                case 76:
                    result = RawType();
                    return result;
            }
            jj_la1[87] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        return result;
    }

    public static final TypeReference RawType() throws ParseException {
        TypeReference result;
        UncollatedReferenceQualifier qn;
        int dimension = 0;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 16:
            case 18:
            case 21:
            case 27:
            case 34:
            case 41:
            case 43:
            case 52:
                result = PrimitiveType();
                break;
            case 76:
                qn = Name();
                result = qn.toTypeReference();
                break;
            default:
                jj_la1[88] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
        }
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 83:
                    break;
                default:
                    jj_la1[89] = jj_gen;
                    break;
            }
            jj_consume_token(83);
            jj_consume_token(84);
            if (dimension == 0)
                setPrefixInfo(result);
            dimension++;
        }
        result.setDimensions(dimension);
        setPostfixInfo(result);
        return result;
    }

    public static final TypeReference PrimitiveType() throws ParseException {
        TypeReference result;
        Identifier id;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 16:
                jj_consume_token(16);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result = factory.createTypeReference(id);
                setPostfixInfo(result);
                return result;
            case 21:
                jj_consume_token(21);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result = factory.createTypeReference(id);
                setPostfixInfo(result);
                return result;
            case 18:
                jj_consume_token(18);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result = factory.createTypeReference(id);
                setPostfixInfo(result);
                return result;
            case 52:
                jj_consume_token(52);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result = factory.createTypeReference(id);
                setPostfixInfo(result);
                return result;
            case 41:
                jj_consume_token(41);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result = factory.createTypeReference(id);
                setPostfixInfo(result);
                return result;
            case 43:
                jj_consume_token(43);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result = factory.createTypeReference(id);
                setPostfixInfo(result);
                return result;
            case 34:
                jj_consume_token(34);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result = factory.createTypeReference(id);
                setPostfixInfo(result);
                return result;
            case 27:
                jj_consume_token(27);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result = factory.createTypeReference(id);
                setPostfixInfo(result);
                return result;
        }
        jj_la1[90] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final TypeReference ResultType() throws ParseException {
        TypeReference result;
        Identifier id;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 63:
                jj_consume_token(63);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result = factory.createTypeReference(id);
                setPrefixInfo(result);
                setPostfixInfo(result);
                return result;
            case 16:
            case 18:
            case 21:
            case 27:
            case 34:
            case 41:
            case 43:
            case 52:
            case 76:
                result = Type();
                setPostfixInfo(result);
                return result;
        }
        jj_la1[91] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final UncollatedReferenceQualifier Name() throws ParseException {
        jj_consume_token(76);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        UncollatedReferenceQualifier result = factory.createUncollatedReferenceQualifier(id);
        while (jj_2_32(2)) {
            jj_consume_token(87);
            setPrefixInfo(result);
            setPostfixInfo(result);
            jj_consume_token(76);
            id = factory.createIdentifier(token.image);
            setPrefixInfo(id);
            setPostfixInfo(id);
            result = factory.createUncollatedReferenceQualifier(result, id);
        }
        setPostfixInfo(result);
        return result;
    }

    public static final UncollatedReferenceQualifier TypedName() throws ParseException {
        ASTList<TypeArgumentDeclaration> typeArguments = null;
        jj_consume_token(76);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        if (jj_2_33(2))
            typeArguments = TypeArguments();
        UncollatedReferenceQualifier result = factory.createUncollatedReferenceQualifier(id);
        result.setTypeArguments(typeArguments);
        while (jj_2_34(2)) {
            jj_consume_token(87);
            setPrefixInfo(result);
            setPostfixInfo(result);
            jj_consume_token(76);
            id = factory.createIdentifier(token.image);
            setPrefixInfo(id);
            setPostfixInfo(id);
            typeArguments = null;
            if (jj_2_35(2))
                typeArguments = TypeArguments();
            result = factory.createUncollatedReferenceQualifier(result, id);
            result.setTypeArguments(typeArguments);
        }
        setPostfixInfo(result);
        return result;
    }

    public static final ASTList<TypeArgumentDeclaration> TypeArguments() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        jj_consume_token(89);
        TypeArgumentDeclaration ta = TypeArgument();
        aSTArrayList.add(ta);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 86:
                    break;
                default:
                    jj_la1[92] = jj_gen;
                    break;
            }
            jj_consume_token(86);
            ta = TypeArgument();
            aSTArrayList.add(ta);
        }
        jj_consume_token(124);
        return (ASTList<TypeArgumentDeclaration>) aSTArrayList;
    }

    public static final TypeArgumentDeclaration TypeArgument() throws ParseException {
        TypeArgument.WildcardMode wm = TypeArgument.WildcardMode.None;
        TypeReference t = null;
        TypeArgumentDeclaration result = new TypeArgumentDeclaration();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 16:
            case 18:
            case 21:
            case 27:
            case 34:
            case 41:
            case 43:
            case 52:
            case 76:
                t = Type();
                setPrefixInfo(result);
                setPostfixInfo(result);
                result.setWildcardMode(wm);
                result.setTypeReference(t);
                return result;
            case 92:
                jj_consume_token(92);
                wm = TypeArgument.WildcardMode.Any;
                setPrefixInfo(result);
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 30:
                    case 54:
                        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                            case 30:
                                jj_consume_token(30);
                                wm = TypeArgument.WildcardMode.Extends;
                                break;
                            case 54:
                                jj_consume_token(54);
                                wm = TypeArgument.WildcardMode.Super;
                                break;
                            default:
                                jj_la1[93] = jj_gen;
                                jj_consume_token(-1);
                                throw new ParseException();
                        }
                        t = Type();
                        setPostfixInfo(result);
                        result.setWildcardMode(wm);
                        result.setTypeReference(t);
                        return result;
                }
                jj_la1[94] = jj_gen;
                setPostfixInfo(result);
                result.setWildcardMode(wm);
                result.setTypeReference(t);
                return result;
        }
        jj_la1[95] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final ASTList<UncollatedReferenceQualifier> TypedNameList() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        UncollatedReferenceQualifier qn = TypedName();
        aSTArrayList.add(qn);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 86:
                    break;
                default:
                    jj_la1[96] = jj_gen;
                    break;
            }
            jj_consume_token(86);
            qn = TypedName();
            aSTArrayList.add(qn);
        }
        return (ASTList<UncollatedReferenceQualifier>) aSTArrayList;
    }

    public static final Expression Expression() throws ParseException {
        Assignment assignment1;
        Expression expr;
        Assignment op;
        ASTArrayList aSTArrayList = new ASTArrayList();
        Expression result = ConditionalExpression();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 88:
            case 111:
            case 112:
            case 113:
            case 114:
            case 115:
            case 116:
            case 117:
            case 118:
            case 119:
            case 120:
            case 121:
                op = AssignmentOperator();
                expr = Expression();
                aSTArrayList.add(result);
                aSTArrayList.add(expr);
                op.setArguments(aSTArrayList);
                assignment1 = op;
                setPostfixInfo(assignment1);
                return assignment1;
        }
        jj_la1[97] = jj_gen;
        setPostfixInfo(assignment1);
        return assignment1;
    }

    public static final Assignment AssignmentOperator() throws ParseException {
        CopyAssignment copyAssignment;
        TimesAssignment timesAssignment;
        DivideAssignment divideAssignment;
        ModuloAssignment moduloAssignment;
        PlusAssignment plusAssignment;
        MinusAssignment minusAssignment;
        ShiftLeftAssignment shiftLeftAssignment;
        ShiftRightAssignment shiftRightAssignment;
        UnsignedShiftRightAssignment unsignedShiftRightAssignment;
        BinaryAndAssignment binaryAndAssignment;
        BinaryXOrAssignment binaryXOrAssignment;
        BinaryOrAssignment binaryOrAssignment;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 88:
                jj_consume_token(88);
                copyAssignment = factory.createCopyAssignment();
                setPostfixInfo(copyAssignment);
                setPrefixInfo(copyAssignment);
                return copyAssignment;
            case 113:
                jj_consume_token(113);
                timesAssignment = factory.createTimesAssignment();
                setPostfixInfo(timesAssignment);
                setPrefixInfo(timesAssignment);
                return timesAssignment;
            case 114:
                jj_consume_token(114);
                divideAssignment = factory.createDivideAssignment();
                setPostfixInfo(divideAssignment);
                setPrefixInfo(divideAssignment);
                return divideAssignment;
            case 118:
                jj_consume_token(118);
                moduloAssignment = factory.createModuloAssignment();
                setPostfixInfo(moduloAssignment);
                setPrefixInfo(moduloAssignment);
                return moduloAssignment;
            case 111:
                jj_consume_token(111);
                plusAssignment = factory.createPlusAssignment();
                setPostfixInfo(plusAssignment);
                setPrefixInfo(plusAssignment);
                return plusAssignment;
            case 112:
                jj_consume_token(112);
                minusAssignment = factory.createMinusAssignment();
                setPostfixInfo(minusAssignment);
                setPrefixInfo(minusAssignment);
                return minusAssignment;
            case 119:
                jj_consume_token(119);
                shiftLeftAssignment = factory.createShiftLeftAssignment();
                setPostfixInfo(shiftLeftAssignment);
                setPrefixInfo(shiftLeftAssignment);
                return shiftLeftAssignment;
            case 120:
                jj_consume_token(120);
                shiftRightAssignment = factory.createShiftRightAssignment();
                setPostfixInfo(shiftRightAssignment);
                setPrefixInfo(shiftRightAssignment);
                return shiftRightAssignment;
            case 121:
                jj_consume_token(121);
                unsignedShiftRightAssignment = factory.createUnsignedShiftRightAssignment();
                setPostfixInfo(unsignedShiftRightAssignment);
                setPrefixInfo(unsignedShiftRightAssignment);
                return unsignedShiftRightAssignment;
            case 115:
                jj_consume_token(115);
                binaryAndAssignment = factory.createBinaryAndAssignment();
                setPostfixInfo(binaryAndAssignment);
                setPrefixInfo(binaryAndAssignment);
                return binaryAndAssignment;
            case 117:
                jj_consume_token(117);
                binaryXOrAssignment = factory.createBinaryXOrAssignment();
                setPostfixInfo(binaryXOrAssignment);
                setPrefixInfo(binaryXOrAssignment);
                return binaryXOrAssignment;
            case 116:
                jj_consume_token(116);
                binaryOrAssignment = factory.createBinaryOrAssignment();
                setPostfixInfo(binaryOrAssignment);
                setPrefixInfo(binaryOrAssignment);
                return binaryOrAssignment;
        }
        jj_la1[98] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final Expression ConditionalExpression() throws ParseException {
        Conditional conditional1;
        Expression expr1, expr2;
        Conditional conditional2;
        ASTArrayList aSTArrayList;
        Expression result = ConditionalOrExpression();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 92:
                jj_consume_token(92);
                conditional2 = factory.createConditional();
                setPrefixInfo(conditional2);
                expr1 = Expression();
                jj_consume_token(93);
                expr2 = ConditionalExpression();
                aSTArrayList = new ASTArrayList(3);
                aSTArrayList.add(result);
                aSTArrayList.add(expr1);
                aSTArrayList.add(expr2);
                conditional2.setArguments(aSTArrayList);
                conditional1 = conditional2;
                setPostfixInfo(conditional1);
                return conditional1;
        }
        jj_la1[99] = jj_gen;
        setPostfixInfo(conditional1);
        return conditional1;
    }

    public static final Expression ConditionalOrExpression() throws ParseException {
        LogicalOr logicalOr;
        Expression result = ConditionalAndExpression();
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 98:
                    break;
                default:
                    jj_la1[100] = jj_gen;
                    break;
            }
            jj_consume_token(98);
            LogicalOr logicalOr1 = factory.createLogicalOr();
            setPrefixInfo(logicalOr1);
            Expression expr = ConditionalAndExpression();
            ASTArrayList aSTArrayList = new ASTArrayList(2);
            aSTArrayList.add(result);
            aSTArrayList.add(expr);
            logicalOr1.setArguments(aSTArrayList);
            logicalOr = logicalOr1;
        }
        setPostfixInfo(logicalOr);
        return logicalOr;
    }

    public static final Expression ConditionalAndExpression() throws ParseException {
        LogicalAnd logicalAnd;
        Expression result = InclusiveOrExpression();
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 99:
                    break;
                default:
                    jj_la1[101] = jj_gen;
                    break;
            }
            jj_consume_token(99);
            LogicalAnd logicalAnd1 = factory.createLogicalAnd();
            setPrefixInfo(logicalAnd1);
            Expression expr = InclusiveOrExpression();
            ASTArrayList aSTArrayList = new ASTArrayList(2);
            aSTArrayList.add(result);
            aSTArrayList.add(expr);
            logicalAnd1.setArguments(aSTArrayList);
            logicalAnd = logicalAnd1;
        }
        setPostfixInfo(logicalAnd);
        return logicalAnd;
    }

    public static final Expression InclusiveOrExpression() throws ParseException {
        BinaryOr binaryOr;
        Expression result = ExclusiveOrExpression();
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 107:
                    break;
                default:
                    jj_la1[102] = jj_gen;
                    break;
            }
            jj_consume_token(107);
            BinaryOr binaryOr1 = factory.createBinaryOr();
            setPrefixInfo(binaryOr1);
            Expression expr = ExclusiveOrExpression();
            ASTArrayList aSTArrayList = new ASTArrayList(2);
            aSTArrayList.add(result);
            aSTArrayList.add(expr);
            binaryOr1.setArguments(aSTArrayList);
            binaryOr = binaryOr1;
        }
        setPostfixInfo(binaryOr);
        return binaryOr;
    }

    public static final Expression ExclusiveOrExpression() throws ParseException {
        BinaryXOr binaryXOr;
        Expression result = AndExpression();
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 108:
                    break;
                default:
                    jj_la1[103] = jj_gen;
                    break;
            }
            jj_consume_token(108);
            BinaryXOr binaryXOr1 = factory.createBinaryXOr();
            setPrefixInfo(binaryXOr1);
            Expression expr = AndExpression();
            ASTArrayList aSTArrayList = new ASTArrayList(2);
            aSTArrayList.add(result);
            aSTArrayList.add(expr);
            binaryXOr1.setArguments(aSTArrayList);
            binaryXOr = binaryXOr1;
        }
        setPostfixInfo(binaryXOr);
        return binaryXOr;
    }

    public static final Expression AndExpression() throws ParseException {
        BinaryAnd binaryAnd;
        Expression result = EqualityExpression();
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 106:
                    break;
                default:
                    jj_la1[104] = jj_gen;
                    break;
            }
            jj_consume_token(106);
            BinaryAnd binaryAnd1 = factory.createBinaryAnd();
            setPrefixInfo(binaryAnd1);
            Expression expr = EqualityExpression();
            ASTArrayList aSTArrayList = new ASTArrayList(2);
            aSTArrayList.add(result);
            aSTArrayList.add(expr);
            binaryAnd1.setArguments(aSTArrayList);
            binaryAnd = binaryAnd1;
        }
        setPostfixInfo(binaryAnd);
        return binaryAnd;
    }

    public static final Expression EqualityExpression() throws ParseException {
        NotEquals notEquals;
        Expression result = InstanceOfExpression();
        while (true) {
            Equals equals;
            NotEquals notEquals1;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 94:
                case 97:
                    break;
                default:
                    jj_la1[105] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 94:
                    jj_consume_token(94);
                    equals = factory.createEquals();
                    setPrefixInfo(equals);
                    break;
                case 97:
                    jj_consume_token(97);
                    notEquals1 = factory.createNotEquals();
                    setPrefixInfo(notEquals1);
                    break;
                default:
                    jj_la1[106] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            Expression expr = InstanceOfExpression();
            ASTArrayList aSTArrayList = new ASTArrayList(2);
            aSTArrayList.add(result);
            aSTArrayList.add(expr);
            notEquals1.setArguments(aSTArrayList);
            notEquals = notEquals1;
        }
        setPostfixInfo(notEquals);
        return notEquals;
    }

    public static final Expression InstanceOfExpression() throws ParseException {
        Instanceof instanceof_;
        TypeReference tr;
        Expression result = RelationalExpression();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 40:
                jj_consume_token(40);
                tr = Type();
                instanceof_ = factory.createInstanceof(result, tr);
                setPrefixInfo(instanceof_);
                setPostfixInfo(instanceof_);
                return instanceof_;
        }
        jj_la1[107] = jj_gen;
        setPostfixInfo(instanceof_);
        return instanceof_;
    }

    public static final Expression RelationalExpression() throws ParseException {
        GreaterOrEquals greaterOrEquals;
        Expression result = ShiftExpression();
        while (true) {
            LessThan lessThan;
            GreaterThan greaterThan;
            LessOrEquals lessOrEquals;
            GreaterOrEquals greaterOrEquals1;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 89:
                case 95:
                case 96:
                case 124:
                    break;
                default:
                    jj_la1[108] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 89:
                    jj_consume_token(89);
                    lessThan = factory.createLessThan();
                    setPrefixInfo(lessThan);
                    break;
                case 124:
                    jj_consume_token(124);
                    greaterThan = factory.createGreaterThan();
                    setPrefixInfo(greaterThan);
                    break;
                case 95:
                    jj_consume_token(95);
                    lessOrEquals = factory.createLessOrEquals();
                    setPrefixInfo(lessOrEquals);
                    break;
                case 96:
                    jj_consume_token(96);
                    greaterOrEquals1 = factory.createGreaterOrEquals();
                    setPrefixInfo(greaterOrEquals1);
                    break;
                default:
                    jj_la1[109] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            Expression expr = ShiftExpression();
            ASTArrayList aSTArrayList = new ASTArrayList(2);
            aSTArrayList.add(result);
            aSTArrayList.add(expr);
            greaterOrEquals1.setArguments(aSTArrayList);
            greaterOrEquals = greaterOrEquals1;
        }
        setPostfixInfo(greaterOrEquals);
        return greaterOrEquals;
    }

    public static final Expression ShiftExpression() throws ParseException {
        UnsignedShiftRight unsignedShiftRight;
        Expression result = AdditiveExpression();
        while (jj_2_36(1)) {
            ShiftLeft shiftLeft;
            UnsignedShiftRight unsignedShiftRight1;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 110:
                    jj_consume_token(110);
                    shiftLeft = factory.createShiftLeft();
                    setPrefixInfo(shiftLeft);
                    break;
                default:
                    jj_la1[110] = jj_gen;
                    if (jj_2_37(1)) {
                        RSIGNEDSHIFT();
                        ShiftRight shiftRight = factory.createShiftRight();
                        setPrefixInfo(shiftRight);
                        break;
                    }
                    if (jj_2_38(1)) {
                        RUNSIGNEDSHIFT();
                        unsignedShiftRight1 = factory.createUnsignedShiftRight();
                        setPrefixInfo(unsignedShiftRight1);
                        break;
                    }
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            Expression expr = AdditiveExpression();
            ASTArrayList aSTArrayList = new ASTArrayList(2);
            aSTArrayList.add(result);
            aSTArrayList.add(expr);
            unsignedShiftRight1.setArguments(aSTArrayList);
            unsignedShiftRight = unsignedShiftRight1;
        }
        setPostfixInfo(unsignedShiftRight);
        return unsignedShiftRight;
    }

    public static final Expression AdditiveExpression() throws ParseException {
        Minus minus;
        Expression result = MultiplicativeExpression();
        while (true) {
            Plus plus;
            Minus minus1;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 102:
                case 103:
                    break;
                default:
                    jj_la1[111] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 102:
                    jj_consume_token(102);
                    plus = factory.createPlus();
                    setPrefixInfo(plus);
                    break;
                case 103:
                    jj_consume_token(103);
                    minus1 = factory.createMinus();
                    setPrefixInfo(minus1);
                    break;
                default:
                    jj_la1[112] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            Expression expr = MultiplicativeExpression();
            ASTArrayList aSTArrayList = new ASTArrayList(2);
            aSTArrayList.add(result);
            aSTArrayList.add(expr);
            minus1.setArguments(aSTArrayList);
            minus = minus1;
        }
        setPostfixInfo(minus);
        return minus;
    }

    public static final Expression MultiplicativeExpression() throws ParseException {
        Modulo modulo;
        Expression result = null;
        Operator mult = null;
        result = UnaryExpression();
        while (true) {
            Times times;
            Divide divide;
            Modulo modulo1;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 104:
                case 105:
                case 109:
                    break;
                default:
                    jj_la1[113] = jj_gen;
                    break;
            }
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 104:
                    jj_consume_token(104);
                    times = factory.createTimes();
                    setPrefixInfo(times);
                    break;
                case 105:
                    jj_consume_token(105);
                    divide = factory.createDivide();
                    setPrefixInfo(divide);
                    break;
                case 109:
                    jj_consume_token(109);
                    modulo1 = factory.createModulo();
                    setPrefixInfo(modulo1);
                    break;
                default:
                    jj_la1[114] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            Expression expr = UnaryExpression();
            ASTArrayList aSTArrayList = new ASTArrayList(2);
            aSTArrayList.add(result);
            aSTArrayList.add(expr);
            modulo1.setArguments(aSTArrayList);
            modulo = modulo1;
        }
        setPostfixInfo(modulo);
        return modulo;
    }

    public static final Expression UnaryExpression() throws ParseException {
        Positive positive;
        Negative negative1;
        PreIncrement preIncrement;
        PreDecrement preDecrement;
        Expression expression1, expr;
        boolean negative = false;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 102:
            case 103:
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 102:
                        jj_consume_token(102);
                        positive = factory.createPositive();
                        setPrefixInfo(positive);
                        break;
                    case 103:
                        jj_consume_token(103);
                        negative1 = factory.createNegative();
                        setPrefixInfo(negative1);
                        break;
                    default:
                        jj_la1[115] = jj_gen;
                        jj_consume_token(-1);
                        throw new ParseException();
                }
                expr = UnaryExpression();
                negative1.setArguments(new ASTArrayList(expr));
                setPostfixInfo(negative1);
                return negative1;
            case 100:
                preIncrement = PreIncrementExpression();
                setPostfixInfo(preIncrement);
                return preIncrement;
            case 101:
                preDecrement = PreDecrementExpression();
                setPostfixInfo(preDecrement);
                return preDecrement;
            case 16:
            case 18:
            case 21:
            case 27:
            case 31:
            case 34:
            case 41:
            case 43:
            case 45:
            case 46:
            case 52:
            case 54:
            case 57:
            case 61:
            case 63:
            case 68:
            case 72:
            case 74:
            case 75:
            case 76:
            case 79:
            case 90:
            case 91:
                expression1 = UnaryExpressionNotPlusMinus();
                setPostfixInfo(expression1);
                return expression1;
        }
        jj_la1[116] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final PreIncrement PreIncrementExpression() throws ParseException {
        jj_consume_token(100);
        PreIncrement result = factory.createPreIncrement();
        setPrefixInfo(result);
        Expression expr = PrimaryExpression();
        result.setArguments(new ASTArrayList(expr));
        setPostfixInfo(result);
        return result;
    }

    public static final PreDecrement PreDecrementExpression() throws ParseException {
        jj_consume_token(101);
        PreDecrement result = factory.createPreDecrement();
        setPrefixInfo(result);
        Expression expr = PrimaryExpression();
        result.setArguments(new ASTArrayList(expr));
        setPostfixInfo(result);
        return result;
    }

    public static final Expression UnaryExpressionNotPlusMinus() throws ParseException {
        BinaryNot binaryNot;
        LogicalNot logicalNot;
        Expression result, expr;
        boolean not = false;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 90:
            case 91:
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 91:
                        jj_consume_token(91);
                        binaryNot = factory.createBinaryNot();
                        setPrefixInfo(binaryNot);
                        break;
                    case 90:
                        jj_consume_token(90);
                        logicalNot = factory.createLogicalNot();
                        setPrefixInfo(logicalNot);
                        break;
                    default:
                        jj_la1[117] = jj_gen;
                        jj_consume_token(-1);
                        throw new ParseException();
                }
                expr = UnaryExpression();
                logicalNot.setArguments(new ASTArrayList(expr));
                setPostfixInfo(logicalNot);
                return logicalNot;
        }
        jj_la1[118] = jj_gen;
        if (jj_2_39(2147483647)) {
            TypeCast typeCast = CastExpression();
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 16:
                case 18:
                case 21:
                case 27:
                case 31:
                case 34:
                case 41:
                case 43:
                case 45:
                case 46:
                case 52:
                case 54:
                case 57:
                case 61:
                case 63:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                    result = PostfixExpression();
                    setPostfixInfo(result);
                    return result;
            }
            jj_la1[119] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(result);
        return result;
    }

    public static final void CastLookahead() throws ParseException {
        if (jj_2_40(2147483647)) {
            jj_consume_token(79);
            PrimitiveType();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 83:
                        break;
                    default:
                        jj_la1[120] = jj_gen;
                        break;
                }
                jj_consume_token(83);
                jj_consume_token(84);
            }
            jj_consume_token(80);
        } else if (jj_2_41(2147483647)) {
            jj_consume_token(79);
            TypedName();
            jj_consume_token(83);
            jj_consume_token(84);
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 79:
                    jj_consume_token(79);
                    TypedName();
                    jj_consume_token(80);
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case 91:
                            jj_consume_token(91);
                            return;
                        case 90:
                            jj_consume_token(90);
                            return;
                        case 79:
                            jj_consume_token(79);
                            return;
                        case 76:
                            jj_consume_token(76);
                            return;
                        case 57:
                            jj_consume_token(57);
                            return;
                        case 54:
                            jj_consume_token(54);
                            return;
                        case 45:
                            jj_consume_token(45);
                            return;
                        case 31:
                        case 46:
                        case 61:
                        case 68:
                        case 72:
                        case 74:
                        case 75:
                            Literal();
                            return;
                    }
                    jj_la1[121] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            jj_la1[122] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
    }

    public static final Expression PostfixExpression() throws ParseException {
        PostIncrement postIncrement;
        PostDecrement postDecrement;
        Expression result = PrimaryExpression();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 100:
            case 101:
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 100:
                        jj_consume_token(100);
                        postIncrement = factory.createPostIncrement(result);
                        setPrefixInfo(postIncrement);
                        setPostfixInfo(postIncrement);
                        return postIncrement;
                    case 101:
                        jj_consume_token(101);
                        postDecrement = factory.createPostDecrement(postIncrement);
                        setPrefixInfo(postDecrement);
                        setPostfixInfo(postDecrement);
                        return postDecrement;
                }
                jj_la1[123] = jj_gen;
                jj_consume_token(-1);
                throw new ParseException();
        }
        jj_la1[124] = jj_gen;
        setPostfixInfo(postDecrement);
        return postDecrement;
    }

    public static final TypeCast CastExpression() throws ParseException {
        TypeReference tr;
        Expression expr;
        TypeCast result = null;
        result = factory.createTypeCast();
        if (jj_2_42(2147483647)) {
            jj_consume_token(79);
            setPrefixInfo(result);
            tr = Type();
            jj_consume_token(80);
            expr = UnaryExpression();
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 79:
                    jj_consume_token(79);
                    setPrefixInfo(result);
                    tr = Type();
                    jj_consume_token(80);
                    expr = UnaryExpressionNotPlusMinus();
                    result.setTypeReference(tr);
                    result.setArguments(new ASTArrayList(expr));
                    setPostfixInfo(result);
                    return result;
            }
            jj_la1[125] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        result.setTypeReference(tr);
        result.setArguments(new ASTArrayList(expr));
        setPostfixInfo(result);
        return result;
    }

    public static final Expression PrimaryExpression() throws ParseException {
        Literal literal;
        Expression expression1;
        ThisReference thisReference;
        UncollatedReferenceQualifier uncollatedReferenceQualifier2;
        ParenthesizedExpression parenthesizedExpression;
        ReferencePrefix referencePrefix1;
        MetaClassReference metaClassReference;
        UncollatedReferenceQualifier uncollatedReferenceQualifier1;
        MethodReference methodReference;
        Expression result = null;
        ReferencePrefix tmpResult = null;
        prefix = PrimaryPrefix();
        switch (prefix.type) {
            case 0:
                if (prefix.literal instanceof StringLiteral) {
                    StringLiteral stringLiteral = (StringLiteral) prefix.literal;
                    break;
                }
                literal = prefix.literal;
                setPostfixInfo(literal);
                return literal;
            case 1:
                thisReference = factory.createThisReference();
                setPrefixInfo(thisReference);
                setPostfixInfo(thisReference);
                break;
            case 2:
                uncollatedReferenceQualifier2 = prefix.name;
                break;
            case 3:
                parenthesizedExpression = (ParenthesizedExpression) prefix.expr;
                break;
            case 4:
                referencePrefix1 = (ReferencePrefix) prefix.expr;
                break;
            case 5:
                metaClassReference = factory.createMetaClassReference(prefix.typeref);
                setPrefixInfo(metaClassReference);
                setPostfixInfo(metaClassReference);
                break;
            case 6:
                uncollatedReferenceQualifier1 = prefix.name;
                break;
            default:
                throw new ParseException("Unknown prefix");
        }
        while (jj_2_43(2)) {
            ThisReference thisReference1;
            SuperReference superReference;
            New new_;
            ArrayReference arrayReference;
            UncollatedReferenceQualifier uncollatedReferenceQualifier;
            suffix = PrimarySuffix();
            switch (suffix.type) {
                case 0:
                    if (uncollatedReferenceQualifier1 instanceof TypeReference) {
                        thisReference1 = factory.createThisReference((TypeReference) uncollatedReferenceQualifier1);
                        setPrefixInfo(thisReference1);
                        setPostfixInfo(thisReference1);
                        continue;
                    }
                    if (thisReference1 instanceof UncollatedReferenceQualifier) {
                        thisReference1 = factory.createThisReference(((UncollatedReferenceQualifier) thisReference1).toTypeReference());
                        setPrefixInfo(thisReference1);
                        setPostfixInfo(thisReference1);
                        continue;
                    }
                    throw new ParseException("No type as prefix of `this'");
                case 5:
                    if (thisReference1 instanceof TypeReference) {
                        superReference = factory.createSuperReference(thisReference1);
                        setPrefixInfo(superReference);
                        setPostfixInfo(superReference);
                        continue;
                    }
                    if (superReference instanceof UncollatedReferenceQualifier) {
                        superReference = factory.createSuperReference(((UncollatedReferenceQualifier) superReference).toTypeReference());
                        setPrefixInfo(superReference);
                        setPostfixInfo(superReference);
                        continue;
                    }
                    if (superReference instanceof ThisReference) {
                        superReference = factory.createSuperReference(superReference);
                        setPrefixInfo(superReference);
                        setPostfixInfo(superReference);
                        continue;
                    }
                    throw new ParseException("No type as prefix of `super', was " + superReference.getClass());
                case 1:
                    if (suffix.expr instanceof New) {
                        ((New) suffix.expr).setReferencePrefix(superReference);
                        new_ = (New) suffix.expr;
                        continue;
                    }
                    throw new ParseException("Allocation without new?");
                case 2:
                    if (new_ instanceof UncollatedReferenceQualifier || new_ instanceof MethodReference || new_ instanceof ParenthesizedExpression || new_ instanceof recoder.java.reference.VariableReference) {
                        ASTArrayList aSTArrayList = new ASTArrayList(1);
                        aSTArrayList.add(suffix.expr);
                        arrayReference = factory.createArrayReference(new_, aSTArrayList);
                        setPrefixInfo(arrayReference);
                        setPostfixInfo(arrayReference);
                        continue;
                    }
                    if (arrayReference instanceof ArrayReference) {
                        arrayReference.getDimensionExpressions().add(suffix.expr);
                        continue;
                    }
                    throw new ParseException("Bad index context - " + arrayReference.getClass().getName() + "?!");
                case 3:
                    uncollatedReferenceQualifier = factory.createUncollatedReferenceQualifier(arrayReference, suffix.id);
                    uncollatedReferenceQualifier.setTypeArguments(suffix.typeArgs);
                    suffix.typeArgs = null;
                    setPrefixInfo(uncollatedReferenceQualifier);
                    setPostfixInfo(uncollatedReferenceQualifier);
                    continue;
                case 4:
                    if (uncollatedReferenceQualifier instanceof UncollatedReferenceQualifier) {
                        methodReference = factory.createMethodReference(uncollatedReferenceQualifier.getReferencePrefix(), uncollatedReferenceQualifier.getIdentifier(), suffix.args, uncollatedReferenceQualifier.getTypeArguments());
                        setPrefixInfo(methodReference);
                        setPostfixInfo(methodReference);
                        continue;
                    }
                    throw new ParseException("Arguments without method name?");
            }
            throw new ParseException("Unknown primary suffix type");
        }
        if (methodReference instanceof UncollatedReferenceQualifier) {
            UncollatedReferenceQualifier uncollatedReferenceQualifier = (UncollatedReferenceQualifier) methodReference;
        } else {
            expression1 = methodReference;
        }
        setPostfixInfo(expression1);
        return expression1;
    }

    public static final PrimaryPrefixReturnValue PrimaryPrefix() throws ParseException {
        Literal lit;
        Expression expr;
        TypeOperator typeOperator;
        SuperReference supRef = null;
        ParenthesizedExpression parExpr = null;
        Identifier id = null;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 31:
            case 46:
            case 61:
            case 68:
            case 72:
            case 74:
            case 75:
                lit = Literal();
                prefix.type = 0;
                prefix.literal = lit;
                return prefix;
            case 57:
                jj_consume_token(57);
                prefix.type = 1;
                return prefix;
            case 54:
                jj_consume_token(54);
                supRef = factory.createSuperReference();
                setPrefixInfo(supRef);
                setPostfixInfo(supRef);
                jj_consume_token(87);
                jj_consume_token(76);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                prefix.name = factory.createUncollatedReferenceQualifier(supRef, id);
                prefix.type = 2;
                return prefix;
            case 79:
                jj_consume_token(79);
                parExpr = factory.createParenthesizedExpression();
                setPrefixInfo(parExpr);
                expr = Expression();
                jj_consume_token(80);
                setPostfixInfo(parExpr);
                parExpr.setArguments(new ASTArrayList(expr));
                prefix.expr = parExpr;
                prefix.type = 3;
                return prefix;
            case 45:
                typeOperator = AllocationExpression();
                prefix.type = 4;
                prefix.expr = typeOperator;
                return prefix;
        }
        jj_la1[126] = jj_gen;
        if (jj_2_44(2147483647)) {
            TypeReference tr = ResultType();
            jj_consume_token(87);
            jj_consume_token(22);
            prefix.type = 5;
            prefix.typeref = tr;
        } else {
            UncollatedReferenceQualifier qn;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 76:
                    qn = Name();
                    prefix.type = 6;
                    prefix.name = qn;
                    return prefix;
            }
            jj_la1[127] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        return prefix;
    }

    public static final PrimarySuffixReturnValue PrimarySuffix() throws ParseException {
        if (jj_2_45(2)) {
            jj_consume_token(87);
            jj_consume_token(57);
            suffix.type = 0;
        } else if (jj_2_46(2) && isSuperAllowed()) {
            jj_consume_token(87);
            jj_consume_token(54);
            suffix.type = 5;
        } else if (jj_2_47(2)) {
            jj_consume_token(87);
            TypeOperator typeOperator = AllocationExpression();
            suffix.type = 1;
            suffix.expr = typeOperator;
        } else if (jj_2_48(3)) {
            jj_consume_token(87);
            suffix.typeArgs = NonWildcardTypeArguments();
            jj_consume_token(76);
            suffix.type = 3;
            suffix.id = factory.createIdentifier(token.image);
            setPrefixInfo(suffix.id);
            setPostfixInfo(suffix.id);
        } else {
            Expression expr;
            ASTList<Expression> args;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 83:
                    jj_consume_token(83);
                    expr = Expression();
                    jj_consume_token(84);
                    suffix.type = 2;
                    suffix.expr = expr;
                    return suffix;
                case 87:
                    jj_consume_token(87);
                    jj_consume_token(76);
                    suffix.type = 3;
                    suffix.id = factory.createIdentifier(token.image);
                    setPrefixInfo(suffix.id);
                    setPostfixInfo(suffix.id);
                    return suffix;
                case 79:
                    args = Arguments();
                    suffix.type = 4;
                    suffix.args = args;
                    return suffix;
            }
            jj_la1[128] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        return suffix;
    }

    public static final Literal Literal() throws ParseException {
        IntLiteral intLiteral;
        DoubleLiteral doubleLiteral;
        CharLiteral charLiteral;
        StringLiteral stringLiteral;
        BooleanLiteral booleanLiteral;
        NullLiteral nullLiteral;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 68:
                jj_consume_token(68);
                if (token.image.endsWith("L") || token.image.endsWith("l")) {
                    LongLiteral longLiteral = factory.createLongLiteral(token.image);
                } else {
                    intLiteral = factory.createIntLiteral(token.image);
                }
                setPrefixInfo(intLiteral);
                setPostfixInfo(intLiteral);
                return intLiteral;
            case 72:
                jj_consume_token(72);
                if (token.image.endsWith("F") || token.image.endsWith("f")) {
                    FloatLiteral floatLiteral = factory.createFloatLiteral(token.image);
                } else {
                    doubleLiteral = factory.createDoubleLiteral(token.image);
                }
                setPrefixInfo(doubleLiteral);
                setPostfixInfo(doubleLiteral);
                return doubleLiteral;
            case 74:
                jj_consume_token(74);
                charLiteral = factory.createCharLiteral(token.image);
                setPrefixInfo(charLiteral);
                setPostfixInfo(charLiteral);
                return charLiteral;
            case 75:
                jj_consume_token(75);
                stringLiteral = factory.createStringLiteral(token.image);
                setPrefixInfo(stringLiteral);
                setPostfixInfo(stringLiteral);
                return stringLiteral;
            case 31:
            case 61:
                booleanLiteral = BooleanLiteral();
                setPostfixInfo(booleanLiteral);
                return booleanLiteral;
            case 46:
                nullLiteral = NullLiteral();
                setPostfixInfo(nullLiteral);
                return nullLiteral;
        }
        jj_la1[129] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final BooleanLiteral BooleanLiteral() throws ParseException {
        BooleanLiteral result;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 61:
                jj_consume_token(61);
                result = factory.createBooleanLiteral(true);
                setPrefixInfo(result);
                setPostfixInfo(result);
                return result;
            case 31:
                jj_consume_token(31);
                result = factory.createBooleanLiteral(false);
                setPrefixInfo(result);
                setPostfixInfo(result);
                return result;
        }
        jj_la1[130] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final NullLiteral NullLiteral() throws ParseException {
        jj_consume_token(46);
        NullLiteral result = factory.createNullLiteral();
        setPrefixInfo(result);
        return result;
    }

    public static final ASTList<Expression> Arguments() throws ParseException {
        ASTList<Expression> result = null;
        jj_consume_token(79);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 16:
            case 18:
            case 21:
            case 27:
            case 31:
            case 34:
            case 41:
            case 43:
            case 45:
            case 46:
            case 52:
            case 54:
            case 57:
            case 61:
            case 63:
            case 68:
            case 72:
            case 74:
            case 75:
            case 76:
            case 79:
            case 90:
            case 91:
            case 100:
            case 101:
            case 102:
            case 103:
                result = ArgumentList();
                jj_consume_token(80);
                return result;
        }
        jj_la1[131] = jj_gen;
        jj_consume_token(80);
        return result;
    }

    public static final ASTList<Expression> ArgumentList() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        Expression expr = Expression();
        aSTArrayList.add(expr);
        while (jj_2_49(2147483647)) {
            jj_consume_token(86);
            expr = Expression();
            aSTArrayList.add(expr);
        }
        return (ASTList<Expression>) aSTArrayList;
    }

    public static final TypeOperator AllocationExpression() throws ParseException {
        NewArray newArray;
        ASTList<MemberDeclaration> body = null;
        ClassDeclaration cd = null;
        if (jj_2_50(2)) {
            jj_consume_token(45);
            NewArray na = factory.createNewArray();
            setPrefixInfo(na);
            TypeReference tr = PrimitiveType();
            na.setTypeReference(tr);
            newArray = ArrayDimsAndInits(na);
        } else {
            UncollatedReferenceQualifier qn;
            New new_;
            ASTList<Expression> args;
            NewArray na;
            ASTList<TypeArgumentDeclaration> typeArgs;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 45:
                    jj_consume_token(45);
                    new_ = factory.createNew();
                    setPrefixInfo(new_);
                    qn = TypedName();
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case 89:
                            typeArgs = NonWildcardTypeArguments();
                            qn.setTypeArguments(typeArgs);
                            break;
                        default:
                            jj_la1[132] = jj_gen;
                            break;
                    }
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case 79:
                            args = Arguments();
                            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                                case 81:
                                    cd = factory.createClassDeclaration();
                                    setPrefixInfo(cd);
                                    body = ClassBody();
                                    cd.setMembers(body);
                                    setPostfixInfo(cd);
                                    break;
                                default:
                                    jj_la1[133] = jj_gen;
                                    break;
                            }
                            new_.setTypeReference(qn.toTypeReference());
                            new_.setArguments(args);
                            if (cd != null)
                                new_.setClassDeclaration(cd);
                            setPostfixInfo(new_);
                            return new_;
                        case 83:
                            na = factory.createNewArray();
                            copyPrefixInfo(new_, na);
                            na.setTypeReference(qn.toTypeReference());
                            newArray = ArrayDimsAndInits(na);
                            setPostfixInfo(newArray);
                            return newArray;
                    }
                    jj_la1[134] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
            jj_la1[135] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(newArray);
        return newArray;
    }

    public static final NewArray ArrayDimsAndInits(NewArray result) throws ParseException {
        int dimensions = 0;
        ASTList<Expression> sizes = null;
        ArrayInitializer init = null;
        if (jj_2_53(2)) {
            while (true) {
                jj_consume_token(83);
                Expression expr = Expression();
                jj_consume_token(84);
                sizes = (sizes == null) ? (ASTList<Expression>) new ASTArrayList() : sizes;
                sizes.add(expr);
                dimensions++;
                if (jj_2_51(2))
                    continue;
                break;
            }
            while (jj_2_52(2)) {
                jj_consume_token(83);
                jj_consume_token(84);
                dimensions++;
            }
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 83:
                    while (true) {
                        jj_consume_token(83);
                        jj_consume_token(84);
                        dimensions++;
                        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                            case 83:
                                continue;
                        }
                        break;
                    }
                    jj_la1[136] = jj_gen;
                    init = ArrayInitializer();
                    break;
                default:
                    jj_la1[137] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
        }
        result.setDimensions(dimensions);
        if (sizes != null)
            result.setArguments(sizes);
        result.setArrayInitializer(init);
        setPostfixInfo(result);
        return result;
    }

    public static final Statement Statement() throws ParseException {
        Assert assert_;
        Statement result = null;
        if (jj_2_54(2)) {
            LabeledStatement labeledStatement = LabeledStatement();
        } else {
            StatementBlock statementBlock;
            EmptyStatement emptyStatement;
            ExpressionStatement expressionStatement;
            Switch switch_;
            If if_;
            While while_;
            Do do_;
            LoopStatement loopStatement;
            Break break_;
            Continue continue_;
            Return return_;
            Throw throw_;
            SynchronizedBlock synchronizedBlock;
            Try try_;
            Expression expr;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 81:
                    statementBlock = Block();
                    setPostfixInfo(statementBlock);
                    return statementBlock;
                case 85:
                    emptyStatement = EmptyStatement();
                    setPostfixInfo(emptyStatement);
                    return emptyStatement;
                case 16:
                case 18:
                case 21:
                case 27:
                case 31:
                case 34:
                case 41:
                case 43:
                case 45:
                case 46:
                case 52:
                case 54:
                case 57:
                case 61:
                case 63:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                case 100:
                case 101:
                    expr = StatementExpression();
                    jj_consume_token(85);
                    try {
                        expressionStatement = (ExpressionStatement) expr;
                    } catch (ClassCastException cce) {
                        throw new ParseException("Class cast error: ExpressionStatement expected - found " + Format.toString("%c @%p %s", expr));
                    }
                    setPostfixInfo(expressionStatement);
                    return expressionStatement;
                case 55:
                    switch_ = SwitchStatement();
                    setPostfixInfo(switch_);
                    return switch_;
                case 37:
                    if_ = IfStatement();
                    setPostfixInfo(if_);
                    return if_;
                case 65:
                    while_ = WhileStatement();
                    setPostfixInfo(while_);
                    return while_;
                case 26:
                    do_ = DoStatement();
                    setPostfixInfo(do_);
                    return do_;
                case 35:
                    loopStatement = ForStatement();
                    setPostfixInfo(loopStatement);
                    return loopStatement;
                case 17:
                    break_ = BreakStatement();
                    setPostfixInfo(break_);
                    return break_;
                case 24:
                    continue_ = ContinueStatement();
                    setPostfixInfo(continue_);
                    return continue_;
                case 51:
                    return_ = ReturnStatement();
                    setPostfixInfo(return_);
                    return return_;
                case 58:
                    throw_ = ThrowStatement();
                    setPostfixInfo(throw_);
                    return throw_;
                case 56:
                    synchronizedBlock = SynchronizedStatement();
                    setPostfixInfo(synchronizedBlock);
                    return synchronizedBlock;
                case 62:
                    try_ = TryStatement();
                    setPostfixInfo(try_);
                    return try_;
                case 14:
                    assert_ = AssertStatement();
                    setPostfixInfo(assert_);
                    return assert_;
            }
            jj_la1[138] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(assert_);
        return assert_;
    }

    public static final LabeledStatement LabeledStatement() throws ParseException {
        jj_consume_token(76);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        jj_consume_token(93);
        LabeledStatement result = factory.createLabeledStatement();
        setPrefixInfo(result);
        result.setIdentifier(id);
        Statement stat = Statement();
        result.setBody(stat);
        setPostfixInfo(result);
        return result;
    }

    public static final StatementBlock Block() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        jj_consume_token(81);
        StatementBlock result = factory.createStatementBlock();
        setPrefixInfo(result);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 14:
                case 15:
                case 16:
                case 17:
                case 18:
                case 21:
                case 22:
                case 24:
                case 26:
                case 27:
                case 31:
                case 32:
                case 34:
                case 35:
                case 37:
                case 41:
                case 43:
                case 45:
                case 46:
                case 51:
                case 52:
                case 54:
                case 55:
                case 56:
                case 57:
                case 58:
                case 61:
                case 62:
                case 63:
                case 65:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                case 81:
                case 85:
                case 100:
                case 101:
                    break;
                default:
                    jj_la1[139] = jj_gen;
                    break;
            }
            Statement stat = BlockStatement();
            aSTArrayList.add(stat);
        }
        jj_consume_token(82);
        result.setBody(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final Statement BlockStatement() throws ParseException {
        ClassDeclaration classDeclaration;
        if (jj_2_55(2147483647)) {
            LocalVariableDeclaration localVariableDeclaration = LocalVariableDeclaration();
            jj_consume_token(85);
        } else {
            Statement result;
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 14:
                case 16:
                case 17:
                case 18:
                case 21:
                case 24:
                case 26:
                case 27:
                case 31:
                case 34:
                case 35:
                case 37:
                case 41:
                case 43:
                case 45:
                case 46:
                case 51:
                case 52:
                case 54:
                case 55:
                case 56:
                case 57:
                case 58:
                case 61:
                case 62:
                case 63:
                case 65:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                case 81:
                case 85:
                case 100:
                case 101:
                    result = Statement();
                    setPostfixInfo(result);
                    return result;
                case 22:
                    classDeclaration = UnmodifiedClassDeclaration();
                    setPostfixInfo(classDeclaration);
                    return classDeclaration;
            }
            jj_la1[140] = jj_gen;
            jj_consume_token(-1);
            throw new ParseException();
        }
        setPostfixInfo(classDeclaration);
        return classDeclaration;
    }

    public static final LocalVariableDeclaration LocalVariableDeclaration() throws ParseException {
        Final fi;
        ASTArrayList aSTArrayList = new ASTArrayList(1);
        ASTArrayList<DeclarationSpecifier> declSpecs = new ASTArrayList();
        LocalVariableDeclaration result = factory.createLocalVariableDeclaration();
        setPrefixInfo(result);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 15:
                    break;
                default:
                    jj_la1[141] = jj_gen;
                    break;
            }
            AnnotationUseSpecification annot = AnnotationUse();
            declSpecs.add(annot);
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 32:
                jj_consume_token(32);
                fi = factory.createFinal();
                setPrefixInfo(fi);
                setPostfixInfo(fi);
                declSpecs.add(fi);
                while (true) {
                    switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                        case 15:
                            break;
                        default:
                            jj_la1[142] = jj_gen;
                            break;
                    }
                    AnnotationUseSpecification annot = AnnotationUse();
                    declSpecs.add(annot);
                }
                break;
            default:
                jj_la1[143] = jj_gen;
                break;
        }
        if (declSpecs.size() != 0)
            result.setDeclarationSpecifiers(declSpecs);
        TypeReference tr = Type();
        VariableSpecification var = VariableDeclarator(false);
        aSTArrayList.add(var);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 86:
                    break;
                default:
                    jj_la1[144] = jj_gen;
                    break;
            }
            jj_consume_token(86);
            var = VariableDeclarator(false);
            aSTArrayList.add(var);
        }
        result.setTypeReference(tr);
        result.setVariableSpecifications(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final EmptyStatement EmptyStatement() throws ParseException {
        jj_consume_token(85);
        EmptyStatement result = factory.createEmptyStatement();
        setPrefixInfo(result);
        setPostfixInfo(result);
        return result;
    }

    public static final Expression StatementExpression() throws ParseException {
        PreIncrement preIncrement;
        PreDecrement preDecrement;
        Expression expression1;
        PostIncrement postIncrement;
        PostDecrement postDecrement;
        Assignment assignment1;
        Expression expr;
        Assignment op;
        ASTArrayList aSTArrayList;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 100:
                preIncrement = PreIncrementExpression();
                setPostfixInfo(preIncrement);
                return preIncrement;
            case 101:
                preDecrement = PreDecrementExpression();
                setPostfixInfo(preDecrement);
                return preDecrement;
            case 16:
            case 18:
            case 21:
            case 27:
            case 31:
            case 34:
            case 41:
            case 43:
            case 45:
            case 46:
            case 52:
            case 54:
            case 57:
            case 61:
            case 63:
            case 68:
            case 72:
            case 74:
            case 75:
            case 76:
            case 79:
                expression1 = PrimaryExpression();
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 88:
                    case 100:
                    case 101:
                    case 111:
                    case 112:
                    case 113:
                    case 114:
                    case 115:
                    case 116:
                    case 117:
                    case 118:
                    case 119:
                    case 120:
                    case 121:
                        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                            case 100:
                                jj_consume_token(100);
                                postIncrement = factory.createPostIncrement(expression1);
                                setPrefixInfo(postIncrement);
                                setPostfixInfo(postIncrement);
                                return postIncrement;
                            case 101:
                                jj_consume_token(101);
                                postDecrement = factory.createPostDecrement(postIncrement);
                                setPrefixInfo(postDecrement);
                                setPostfixInfo(postDecrement);
                                return postDecrement;
                            case 88:
                            case 111:
                            case 112:
                            case 113:
                            case 114:
                            case 115:
                            case 116:
                            case 117:
                            case 118:
                            case 119:
                            case 120:
                            case 121:
                                op = AssignmentOperator();
                                expr = Expression();
                                aSTArrayList = new ASTArrayList(2);
                                aSTArrayList.add(postDecrement);
                                aSTArrayList.add(expr);
                                op.setArguments(aSTArrayList);
                                assignment1 = op;
                                setPostfixInfo(assignment1);
                                return assignment1;
                        }
                        jj_la1[145] = jj_gen;
                        jj_consume_token(-1);
                        throw new ParseException();
                }
                jj_la1[146] = jj_gen;
                setPostfixInfo(assignment1);
                return assignment1;
        }
        jj_la1[147] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final Switch SwitchStatement() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList(2);
        jj_consume_token(55);
        Switch result = factory.createSwitch();
        setPrefixInfo(result);
        jj_consume_token(79);
        Expression expr = Expression();
        jj_consume_token(80);
        jj_consume_token(81);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 19:
                case 25:
                    break;
                default:
                    jj_la1[148] = jj_gen;
                    break;
            }
            Branch branch = SwitchLabel();
            ASTArrayList aSTArrayList1 = new ASTArrayList();
            while (true) {
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 14:
                    case 15:
                    case 16:
                    case 17:
                    case 18:
                    case 21:
                    case 22:
                    case 24:
                    case 26:
                    case 27:
                    case 31:
                    case 32:
                    case 34:
                    case 35:
                    case 37:
                    case 41:
                    case 43:
                    case 45:
                    case 46:
                    case 51:
                    case 52:
                    case 54:
                    case 55:
                    case 56:
                    case 57:
                    case 58:
                    case 61:
                    case 62:
                    case 63:
                    case 65:
                    case 68:
                    case 72:
                    case 74:
                    case 75:
                    case 76:
                    case 79:
                    case 81:
                    case 85:
                    case 100:
                    case 101:
                        break;
                    default:
                        jj_la1[149] = jj_gen;
                        break;
                }
                Statement stat = BlockStatement();
                aSTArrayList1.add(stat);
            }
            if (branch instanceof Case) {
                ((Case) branch).setBody(aSTArrayList1);
            } else {
                ((Default) branch).setBody(aSTArrayList1);
            }
            aSTArrayList.add(branch);
        }
        jj_consume_token(82);
        result.setExpression(expr);
        result.setBranchList(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final Branch SwitchLabel() throws ParseException {
        Case case_;
        Default default_;
        Expression expr;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 19:
                jj_consume_token(19);
                case_ = factory.createCase();
                setPrefixInfo(case_);
                expr = Expression();
                jj_consume_token(93);
                case_.setExpression(expr);
                setPostfixInfo(case_);
                return case_;
            case 25:
                jj_consume_token(25);
                default_ = factory.createDefault();
                setPrefixInfo(default_);
                jj_consume_token(93);
                setPostfixInfo(default_);
                return default_;
        }
        jj_la1[150] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final Assert AssertStatement() throws ParseException {
        Expression cond = null;
        Expression msg = null;
        jj_consume_token(14);
        Assert result = factory.createAssert();
        setPrefixInfo(result);
        cond = Expression();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 93:
                jj_consume_token(93);
                msg = Expression();
                jj_consume_token(85);
                result.setCondition(cond);
                result.setMessage(msg);
                setPostfixInfo(result);
                return result;
        }
        jj_la1[151] = jj_gen;
        jj_consume_token(85);
        result.setCondition(cond);
        result.setMessage(msg);
        setPostfixInfo(result);
        return result;
    }

    public static final If IfStatement() throws ParseException {
        Else elseStat = null;
        Statement falseStat = null;
        jj_consume_token(37);
        If result = factory.createIf();
        setPrefixInfo(result);
        jj_consume_token(79);
        Expression cond = Expression();
        jj_consume_token(80);
        Then thenStat = factory.createThen();
        setPrefixInfo(thenStat);
        Statement trueStat = Statement();
        thenStat.setBody(trueStat);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 28:
                jj_consume_token(28);
                elseStat = factory.createElse();
                setPrefixInfo(elseStat);
                falseStat = Statement();
                elseStat.setBody(falseStat);
                break;
            default:
                jj_la1[152] = jj_gen;
                break;
        }
        result.setExpression(cond);
        result.setThen(thenStat);
        if (elseStat != null)
            result.setElse(elseStat);
        setPostfixInfo(result);
        return result;
    }

    public static final While WhileStatement() throws ParseException {
        jj_consume_token(65);
        While result = factory.createWhile();
        setPrefixInfo(result);
        jj_consume_token(79);
        Expression expr = Expression();
        jj_consume_token(80);
        Statement stat = Statement();
        result.setGuard(expr);
        result.setBody(stat);
        setPostfixInfo(result);
        return result;
    }

    public static final Do DoStatement() throws ParseException {
        jj_consume_token(26);
        Do result = factory.createDo();
        setPrefixInfo(result);
        Statement stat = Statement();
        jj_consume_token(65);
        jj_consume_token(79);
        Expression expr = Expression();
        jj_consume_token(80);
        jj_consume_token(85);
        result.setGuard(expr);
        result.setBody(stat);
        setPostfixInfo(result);
        return result;
    }

    public static final LoopStatement ForStatement() throws ParseException {
        EnhancedFor enhancedFor;
        ASTList<LoopInitializer> init = null;
        Expression guard = null;
        ASTList<Expression> update = null;
        jj_consume_token(35);
        if (jj_2_56(2147483647)) {
            Statement body;
            For for_ = factory.createFor();
            setPrefixInfo(for_);
            jj_consume_token(79);
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 15:
                case 16:
                case 18:
                case 21:
                case 27:
                case 31:
                case 32:
                case 34:
                case 41:
                case 43:
                case 45:
                case 46:
                case 52:
                case 54:
                case 57:
                case 61:
                case 63:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                case 100:
                case 101:
                    init = ForInit();
                    break;
                default:
                    jj_la1[153] = jj_gen;
                    break;
            }
            jj_consume_token(85);
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 16:
                case 18:
                case 21:
                case 27:
                case 31:
                case 34:
                case 41:
                case 43:
                case 45:
                case 46:
                case 52:
                case 54:
                case 57:
                case 61:
                case 63:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                case 90:
                case 91:
                case 100:
                case 101:
                case 102:
                case 103:
                    guard = Expression();
                    break;
                default:
                    jj_la1[154] = jj_gen;
                    break;
            }
            jj_consume_token(85);
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 16:
                case 18:
                case 21:
                case 27:
                case 31:
                case 34:
                case 41:
                case 43:
                case 45:
                case 46:
                case 52:
                case 54:
                case 57:
                case 61:
                case 63:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                case 100:
                case 101:
                    update = ForUpdate();
                    jj_consume_token(80);
                    body = Statement();
                    for_.setInitializers(init);
                    for_.setGuard(guard);
                    for_.setUpdates(update);
                    for_.setBody(body);
                    setPostfixInfo(for_);
                    return for_;
            }
            jj_la1[155] = jj_gen;
        } else if (jj_2_57(2147483647)) {
            enhancedFor = factory.createEnhancedFor();
            setPrefixInfo(enhancedFor);
            jj_consume_token(79);
            init = ForInit();
            jj_consume_token(93);
            guard = Expression();
        } else {
            jj_consume_token(-1);
            throw new ParseException();
        }
        jj_consume_token(80);
        Statement statement = Statement();
        enhancedFor.setInitializers(init);
        enhancedFor.setGuard(guard);
        enhancedFor.setUpdates(update);
        enhancedFor.setBody(statement);
        setPostfixInfo(enhancedFor);
        return enhancedFor;
    }

    public static final ASTList<LoopInitializer> ForInit() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        LocalVariableDeclaration varDecl = null;
        ASTList<Expression> exprs = null;
        if (jj_2_58(2147483647)) {
            varDecl = LocalVariableDeclaration();
        } else {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 16:
                case 18:
                case 21:
                case 27:
                case 31:
                case 34:
                case 41:
                case 43:
                case 45:
                case 46:
                case 52:
                case 54:
                case 57:
                case 61:
                case 63:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                case 100:
                case 101:
                    exprs = StatementExpressionList();
                    break;
                default:
                    jj_la1[156] = jj_gen;
                    jj_consume_token(-1);
                    throw new ParseException();
            }
        }
        if (varDecl != null) {
            aSTArrayList.add(varDecl);
        } else {
            for (int i = 0, s = exprs.size(); i < s; i++)
                aSTArrayList.add(exprs.get(i));
        }
        return (ASTList<LoopInitializer>) aSTArrayList;
    }

    public static final ASTList<Expression> StatementExpressionList() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        Expression expr = StatementExpression();
        aSTArrayList.add(expr);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 86:
                    break;
                default:
                    jj_la1[157] = jj_gen;
                    break;
            }
            jj_consume_token(86);
            expr = StatementExpression();
            aSTArrayList.add(expr);
        }
        return (ASTList<Expression>) aSTArrayList;
    }

    public static final ASTList<Expression> ForUpdate() throws ParseException {
        ASTList<Expression> result = StatementExpressionList();
        return result;
    }

    public static final Break BreakStatement() throws ParseException {
        Identifier id = null;
        jj_consume_token(17);
        Break result = factory.createBreak();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 76:
                jj_consume_token(76);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result.setIdentifier(id);
                jj_consume_token(85);
                setPostfixInfo(result);
                return result;
        }
        jj_la1[158] = jj_gen;
        jj_consume_token(85);
        setPostfixInfo(result);
        return result;
    }

    public static final Continue ContinueStatement() throws ParseException {
        Identifier id = null;
        jj_consume_token(24);
        Continue result = factory.createContinue();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 76:
                jj_consume_token(76);
                id = factory.createIdentifier(token.image);
                setPrefixInfo(id);
                setPostfixInfo(id);
                result.setIdentifier(id);
                jj_consume_token(85);
                setPostfixInfo(result);
                return result;
        }
        jj_la1[159] = jj_gen;
        jj_consume_token(85);
        setPostfixInfo(result);
        return result;
    }

    public static final Return ReturnStatement() throws ParseException {
        Expression expr = null;
        jj_consume_token(51);
        Return result = factory.createReturn();
        setPrefixInfo(result);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 16:
            case 18:
            case 21:
            case 27:
            case 31:
            case 34:
            case 41:
            case 43:
            case 45:
            case 46:
            case 52:
            case 54:
            case 57:
            case 61:
            case 63:
            case 68:
            case 72:
            case 74:
            case 75:
            case 76:
            case 79:
            case 90:
            case 91:
            case 100:
            case 101:
            case 102:
            case 103:
                expr = Expression();
                result.setExpression(expr);
                jj_consume_token(85);
                setPostfixInfo(result);
                return result;
        }
        jj_la1[160] = jj_gen;
        jj_consume_token(85);
        setPostfixInfo(result);
        return result;
    }

    public static final Throw ThrowStatement() throws ParseException {
        jj_consume_token(58);
        Throw result = factory.createThrow();
        setPrefixInfo(result);
        Expression expr = Expression();
        jj_consume_token(85);
        result.setExpression(expr);
        setPostfixInfo(result);
        return result;
    }

    public static final SynchronizedBlock SynchronizedStatement() throws ParseException {
        jj_consume_token(56);
        SynchronizedBlock result = factory.createSynchronizedBlock();
        setPrefixInfo(result);
        jj_consume_token(79);
        Expression expr = Expression();
        jj_consume_token(80);
        StatementBlock block = Block();
        result.setExpression(expr);
        result.setBody(block);
        setPostfixInfo(result);
        return result;
    }

    public static final Try TryStatement() throws ParseException {
        Finally fin;
        ASTArrayList aSTArrayList = new ASTArrayList(1);
        jj_consume_token(62);
        Try result = factory.createTry();
        setPrefixInfo(result);
        StatementBlock block = Block();
        result.setBody(block);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 20:
                    break;
                default:
                    jj_la1[161] = jj_gen;
                    break;
            }
            jj_consume_token(20);
            Catch cat = factory.createCatch();
            setPrefixInfo(cat);
            jj_consume_token(79);
            ParameterDeclaration param = FormalParameter();
            jj_consume_token(80);
            block = Block();
            cat.setParameterDeclaration(param);
            cat.setBody(block);
            aSTArrayList.add(cat);
        }
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 33:
                jj_consume_token(33);
                fin = factory.createFinally();
                setPrefixInfo(fin);
                block = Block();
                fin.setBody(block);
                aSTArrayList.add(fin);
                result.setBranchList(aSTArrayList);
                setPostfixInfo(result);
                return result;
        }
        jj_la1[162] = jj_gen;
        result.setBranchList(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final ASTList<Statement> GeneralizedStatements() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        SpecialConstructorReference scr = null;
        Statement stat = null;
        if (jj_2_59(2147483647)) {
            scr = ExplicitConstructorInvocation();
            aSTArrayList.add(scr);
        }
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 14:
                case 15:
                case 16:
                case 17:
                case 18:
                case 21:
                case 22:
                case 24:
                case 26:
                case 27:
                case 31:
                case 32:
                case 34:
                case 35:
                case 37:
                case 41:
                case 43:
                case 45:
                case 46:
                case 51:
                case 52:
                case 54:
                case 55:
                case 56:
                case 57:
                case 58:
                case 61:
                case 62:
                case 63:
                case 65:
                case 68:
                case 72:
                case 74:
                case 75:
                case 76:
                case 79:
                case 81:
                case 85:
                case 100:
                case 101:
                    break;
                default:
                    jj_la1[163] = jj_gen;
                    break;
            }
            stat = BlockStatement();
            aSTArrayList.add(stat);
        }
        return (ASTList<Statement>) aSTArrayList;
    }

    public static final AnnotationUseSpecification AnnotationUse() throws ParseException {
        ASTArrayList aSTArrayList;
        AnnotationUseSpecification result = factory.createAnnotationUseSpecification();
        Expression ev = null;
        ASTList<AnnotationElementValuePair> list = null;
        jj_consume_token(15);
        setPrefixInfo(result);
        TypeReference tr = Type();
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 79:
                jj_consume_token(79);
                aSTArrayList = new ASTArrayList();
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 15:
                    case 16:
                    case 18:
                    case 21:
                    case 27:
                    case 31:
                    case 34:
                    case 41:
                    case 43:
                    case 45:
                    case 46:
                    case 52:
                    case 54:
                    case 57:
                    case 61:
                    case 63:
                    case 68:
                    case 72:
                    case 74:
                    case 75:
                    case 76:
                    case 79:
                    case 81:
                    case 90:
                    case 91:
                    case 100:
                    case 101:
                    case 102:
                    case 103:
                        if (jj_2_60(2147483647)) {
                            jj_consume_token(76);
                            Identifier ident = factory.createIdentifier(token.image);
                            setPrefixInfo(ident);
                            setPostfixInfo(ident);
                            AnnotationPropertyReference id = factory.createAnnotationPropertyReference(ident);
                            copyPrefixInfo(ident, id);
                            setPostfixInfo(id);
                            jj_consume_token(88);
                            ev = ElementValue();
                            AnnotationElementValuePair evp = new AnnotationElementValuePair(id, ev);
                            copyPrefixInfo(ident, evp);
                            setPostfixInfo(evp);
                            aSTArrayList.add(evp);
                            while (true) {
                                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                                    case 86:
                                        break;
                                    default:
                                        jj_la1[164] = jj_gen;
                                        break;
                                }
                                jj_consume_token(86);
                                jj_consume_token(76);
                                ident = factory.createIdentifier(token.image);
                                setPrefixInfo(ident);
                                setPostfixInfo(ident);
                                id = factory.createAnnotationPropertyReference(ident);
                                copyPrefixInfo(ident, id);
                                setPostfixInfo(id);
                                jj_consume_token(88);
                                ev = ElementValue();
                                evp = new AnnotationElementValuePair(id, ev);
                                copyPrefixInfo(ident, evp);
                                setPostfixInfo(evp);
                                aSTArrayList.add(evp);
                            }
                            break;
                        }
                        if (jj_2_61(2147483647)) {
                            ev = ElementValue();
                            AnnotationElementValuePair evp = new AnnotationElementValuePair(null, ev);
                            copyPrefixInfo(ev, evp);
                            setPostfixInfo(evp);
                            aSTArrayList.add(evp);
                            break;
                        }
                        jj_consume_token(-1);
                        throw new ParseException();
                    default:
                        jj_la1[165] = jj_gen;
                        break;
                }
                jj_consume_token(80);
                break;
            default:
                jj_la1[166] = jj_gen;
                break;
        }
        result.setTypeReference(tr);
        if (aSTArrayList != null)
            result.setElementValuePairs(aSTArrayList);
        setPostfixInfo(result);
        return result;
    }

    public static final Expression ElementValue() throws ParseException {
        AnnotationUseSpecification annotationUseSpecification;
        ElementValueArrayInitializer elementValueArrayInitializer;
        Expression tmp;
        ASTArrayList aSTArrayList;
        Expression res = null;
        ASTList<Expression> elist = null;
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 16:
            case 18:
            case 21:
            case 27:
            case 31:
            case 34:
            case 41:
            case 43:
            case 45:
            case 46:
            case 52:
            case 54:
            case 57:
            case 61:
            case 63:
            case 68:
            case 72:
            case 74:
            case 75:
            case 76:
            case 79:
            case 90:
            case 91:
            case 100:
            case 101:
            case 102:
            case 103:
                res = Expression();
                return res;
            case 15:
                return AnnotationUse();
            case 81:
                jj_consume_token(81);
                elementValueArrayInitializer = new ElementValueArrayInitializer();
                setPrefixInfo(elementValueArrayInitializer);
                switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                    case 15:
                    case 16:
                    case 18:
                    case 21:
                    case 27:
                    case 31:
                    case 34:
                    case 41:
                    case 43:
                    case 45:
                    case 46:
                    case 52:
                    case 54:
                    case 57:
                    case 61:
                    case 63:
                    case 68:
                    case 72:
                    case 74:
                    case 75:
                    case 76:
                    case 79:
                    case 81:
                    case 90:
                    case 91:
                    case 100:
                    case 101:
                    case 102:
                    case 103:
                        tmp = ElementValue();
                        aSTArrayList = new ASTArrayList();
                        aSTArrayList.add(tmp);
                        while (jj_2_62(2)) {
                            jj_consume_token(86);
                            tmp = ElementValue();
                            aSTArrayList.add(tmp);
                        }
                        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                            case 86:
                                jj_consume_token(86);
                                break;
                        }
                        jj_la1[167] = jj_gen;
                        break;
                    default:
                        jj_la1[168] = jj_gen;
                        break;
                }
                jj_consume_token(82);
                setPostfixInfo(elementValueArrayInitializer);
                elementValueArrayInitializer.setElementValues(aSTArrayList);
                return elementValueArrayInitializer;
        }
        jj_la1[169] = jj_gen;
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final ASTList<TypeArgumentDeclaration> NonWildcardTypeArguments() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        jj_consume_token(89);
        ASTList<UncollatedReferenceQualifier> nl = TypedNameList();
        jj_consume_token(124);
        for (int i = 0; i < nl.size(); i++) {
            TypeArgumentDeclaration ta = new TypeArgumentDeclaration(nl.get(i).toTypeReference());
            aSTArrayList.add(ta);
        }
        return (ASTList<TypeArgumentDeclaration>) aSTArrayList;
    }

    public static final ASTList<TypeParameterDeclaration> TypeParametersNoLE() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        TypeParameterDeclaration tp = TypeParameter();
        aSTArrayList.add(tp);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 86:
                    break;
                default:
                    jj_la1[170] = jj_gen;
                    break;
            }
            jj_consume_token(86);
            tp = TypeParameter();
            aSTArrayList.add(tp);
        }
        jj_consume_token(124);
        return (ASTList<TypeParameterDeclaration>) aSTArrayList;
    }

    public static final ASTList<TypeParameterDeclaration> TypeParameters() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        jj_consume_token(89);
        return TypeParametersNoLE();
    }

    public static final TypeParameterDeclaration TypeParameter() throws ParseException {
        TypeParameterDeclaration res = new TypeParameterDeclaration();
        ASTList<TypeReference> bound = null;
        jj_consume_token(76);
        Identifier id = factory.createIdentifier(token.image);
        setPrefixInfo(id);
        setPostfixInfo(id);
        switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
            case 30:
                jj_consume_token(30);
                bound = Bound();
                res.setIdentifier(id);
                res.setBound(bound);
                return res;
        }
        jj_la1[171] = jj_gen;
        res.setIdentifier(id);
        res.setBound(bound);
        return res;
    }

    public static final ASTList<TypeReference> Bound() throws ParseException {
        ASTArrayList aSTArrayList = new ASTArrayList();
        TypeReference tr = Type();
        aSTArrayList.add(tr);
        while (true) {
            switch ((jj_ntk == -1) ? jj_ntk() : jj_ntk) {
                case 106:
                    break;
                default:
                    jj_la1[172] = jj_gen;
                    break;
            }
            jj_consume_token(106);
            tr = Type();
            aSTArrayList.add(tr);
        }
        return (ASTList<TypeReference>) aSTArrayList;
    }

    public static final void RUNSIGNEDSHIFT() throws ParseException {
        if ((getToken(1)).kind == 124 && ((Token.GTToken) getToken(1)).realKind == 122) {
            jj_consume_token(124);
            jj_consume_token(124);
            jj_consume_token(124);
            return;
        }
        jj_consume_token(-1);
        throw new ParseException();
    }

    public static final void RSIGNEDSHIFT() throws ParseException {
        if ((getToken(1)).kind == 124 && ((Token.GTToken) getToken(1)).realKind == 123) {
            jj_consume_token(124);
            jj_consume_token(124);
            return;
        }
        jj_consume_token(-1);
        throw new ParseException();
    }

    private static final boolean jj_2_1(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_1();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(0, xla);
        }
    }

    private static final boolean jj_2_2(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_2();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(1, xla);
        }
    }

    private static final boolean jj_2_3(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_3();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(2, xla);
        }
    }

    private static final boolean jj_2_4(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_4();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(3, xla);
        }
    }

    private static final boolean jj_2_5(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_5();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(4, xla);
        }
    }

    private static final boolean jj_2_6(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_6();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(5, xla);
        }
    }

    private static final boolean jj_2_7(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_7();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(6, xla);
        }
    }

    private static final boolean jj_2_8(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_8();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(7, xla);
        }
    }

    private static final boolean jj_2_9(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_9();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(8, xla);
        }
    }

    private static final boolean jj_2_10(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_10();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(9, xla);
        }
    }

    private static final boolean jj_2_11(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_11();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(10, xla);
        }
    }

    private static final boolean jj_2_12(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_12();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(11, xla);
        }
    }

    private static final boolean jj_2_13(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_13();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(12, xla);
        }
    }

    private static final boolean jj_2_14(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_14();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(13, xla);
        }
    }

    private static final boolean jj_2_15(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_15();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(14, xla);
        }
    }

    private static final boolean jj_2_16(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_16();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(15, xla);
        }
    }

    private static final boolean jj_2_17(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_17();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(16, xla);
        }
    }

    private static final boolean jj_2_18(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_18();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(17, xla);
        }
    }

    private static final boolean jj_2_19(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_19();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(18, xla);
        }
    }

    private static final boolean jj_2_20(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_20();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(19, xla);
        }
    }

    private static final boolean jj_2_21(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_21();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(20, xla);
        }
    }

    private static final boolean jj_2_22(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_22();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(21, xla);
        }
    }

    private static final boolean jj_2_23(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_23();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(22, xla);
        }
    }

    private static final boolean jj_2_24(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_24();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(23, xla);
        }
    }

    private static final boolean jj_2_25(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_25();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(24, xla);
        }
    }

    private static final boolean jj_2_26(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_26();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(25, xla);
        }
    }

    private static final boolean jj_2_27(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_27();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(26, xla);
        }
    }

    private static final boolean jj_2_28(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_28();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(27, xla);
        }
    }

    private static final boolean jj_2_29(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_29();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(28, xla);
        }
    }

    private static final boolean jj_2_30(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_30();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(29, xla);
        }
    }

    private static final boolean jj_2_31(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_31();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(30, xla);
        }
    }

    private static final boolean jj_2_32(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_32();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(31, xla);
        }
    }

    private static final boolean jj_2_33(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_33();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(32, xla);
        }
    }

    private static final boolean jj_2_34(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_34();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(33, xla);
        }
    }

    private static final boolean jj_2_35(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_35();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(34, xla);
        }
    }

    private static final boolean jj_2_36(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_36();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(35, xla);
        }
    }

    private static final boolean jj_2_37(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_37();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(36, xla);
        }
    }

    private static final boolean jj_2_38(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_38();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(37, xla);
        }
    }

    private static final boolean jj_2_39(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_39();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(38, xla);
        }
    }

    private static final boolean jj_2_40(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_40();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(39, xla);
        }
    }

    private static final boolean jj_2_41(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_41();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(40, xla);
        }
    }

    private static final boolean jj_2_42(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_42();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(41, xla);
        }
    }

    private static final boolean jj_2_43(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_43();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(42, xla);
        }
    }

    private static final boolean jj_2_44(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_44();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(43, xla);
        }
    }

    private static final boolean jj_2_45(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_45();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(44, xla);
        }
    }

    private static final boolean jj_2_46(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_46();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(45, xla);
        }
    }

    private static final boolean jj_2_47(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_47();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(46, xla);
        }
    }

    private static final boolean jj_2_48(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_48();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(47, xla);
        }
    }

    private static final boolean jj_2_49(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_49();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(48, xla);
        }
    }

    private static final boolean jj_2_50(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_50();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(49, xla);
        }
    }

    private static final boolean jj_2_51(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_51();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(50, xla);
        }
    }

    private static final boolean jj_2_52(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_52();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(51, xla);
        }
    }

    private static final boolean jj_2_53(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_53();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(52, xla);
        }
    }

    private static final boolean jj_2_54(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_54();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(53, xla);
        }
    }

    private static final boolean jj_2_55(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_55();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(54, xla);
        }
    }

    private static final boolean jj_2_56(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_56();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(55, xla);
        }
    }

    private static final boolean jj_2_57(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_57();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(56, xla);
        }
    }

    private static final boolean jj_2_58(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_58();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(57, xla);
        }
    }

    private static final boolean jj_2_59(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_59();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(58, xla);
        }
    }

    private static final boolean jj_2_60(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_60();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(59, xla);
        }
    }

    private static final boolean jj_2_61(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_61();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(60, xla);
        }
    }

    private static final boolean jj_2_62(int xla) {
        jj_la = xla;
        jj_lastpos = jj_scanpos = token;
        try {
            return !jj_3_62();
        } catch (LookaheadSuccess ls) {
            return true;
        } finally {
            jj_save(61, xla);
        }
    }

    private static final boolean jj_3R_352() {
        return jj_3R_117();
    }

    private static final boolean jj_3R_296() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_149();
    }

    private static final boolean jj_3R_220() {
        return jj_3R_269();
    }

    private static final boolean jj_3_14() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_106();
    }

    private static final boolean jj_3R_344() {
        if (jj_scan_token(101))
            return true;
        return jj_3R_118();
    }

    private static final boolean jj_3R_155() {
        if (jj_scan_token(85))
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_220()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_351() {
        if (jj_scan_token(59))
            return true;
        return jj_3R_188();
    }

    private static final boolean jj_3R_329() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_374() {
        if (jj_scan_token(106))
            return true;
        return jj_3R_94();
    }

    private static final boolean jj_3R_177() {
        return false;
    }

    private static final boolean jj_3R_154() {
        if (jj_3R_106())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3_14()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_295() {
        if (jj_scan_token(32))
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_329()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_294() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_349() {
        return jj_3R_165();
    }

    private static final boolean jj_3R_178() {
        return false;
    }

    private static final boolean jj_3R_387() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_258() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_294()) {
                jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_295())
                    jj_scanpos = xsp;
                if (jj_3R_94())
                    return true;
                if (jj_3R_149())
                    return true;
                while (true) {
                    xsp = jj_scanpos;
                    if (jj_3R_296()) {
                        jj_scanpos = xsp;
                        return false;
                    }
                }
                break;
            }
        }
    }

    private static final boolean jj_3R_123() {
        Token xsp = jj_scanpos;
        lookingAhead = true;
        jj_semLA = ((getToken(1)).kind == 124 && ((Token.GTToken) getToken(1)).realKind == 123);
        lookingAhead = false;
        if (!jj_semLA || jj_3R_177())
            return true;
        if (jj_scan_token(124))
            return true;
        return jj_scan_token(124);
    }

    private static final boolean jj_3R_343() {
        if (jj_scan_token(100))
            return true;
        return jj_3R_118();
    }

    private static final boolean jj_3R_386() {
        return jj_scan_token(48);
    }

    private static final boolean jj_3R_385() {
        return jj_scan_token(49);
    }

    private static final boolean jj_3R_384() {
        return jj_scan_token(50);
    }

    private static final boolean jj_3R_124() {
        Token xsp = jj_scanpos;
        lookingAhead = true;
        jj_semLA = ((getToken(1)).kind == 124 && ((Token.GTToken) getToken(1)).realKind == 122);
        lookingAhead = false;
        if (!jj_semLA || jj_3R_178())
            return true;
        if (jj_scan_token(124))
            return true;
        if (jj_scan_token(124))
            return true;
        return jj_scan_token(124);
    }

    private static final boolean jj_3R_348() {
        Token xsp = jj_scanpos;
        if (jj_3R_384()) {
            jj_scanpos = xsp;
            if (jj_3R_385()) {
                jj_scanpos = xsp;
                if (jj_3R_386())
                    return true;
            }
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_387()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_153() {
        if (jj_scan_token(38))
            return true;
        return jj_3R_188();
    }

    private static final boolean jj_3R_134() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_347() {
        return jj_3R_144();
    }

    private static final boolean jj_3_55() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_134()) {
                jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_scan_token(32))
                    jj_scanpos = xsp;
                if (jj_3R_94())
                    return true;
                return jj_scan_token(76);
            }
        }
    }

    private static final boolean jj_3R_468() {
        return jj_3R_474();
    }

    private static final boolean jj_3R_337() {
        if (jj_3R_94())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_374()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_333() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_347()) {
                jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_348())
                    jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_349())
                    jj_scanpos = xsp;
                if (jj_scan_token(76))
                    return true;
                if (jj_3R_350())
                    return true;
                xsp = jj_scanpos;
                if (jj_3R_351())
                    jj_scanpos = xsp;
                if (jj_scan_token(81))
                    return true;
                xsp = jj_scanpos;
                if (jj_3R_352())
                    jj_scanpos = xsp;
                while (true) {
                    xsp = jj_scanpos;
                    if (jj_3R_353()) {
                        jj_scanpos = xsp;
                        return jj_scan_token(82);
                    }
                }
                break;
            }
        }
    }

    private static final boolean jj_3R_467() {
        return jj_3R_344();
    }

    private static final boolean jj_3R_317() {
        return jj_3R_152();
    }

    private static final boolean jj_3R_466() {
        return jj_3R_343();
    }

    private static final boolean jj_3R_316() {
        return jj_3R_335();
    }

    private static final boolean jj_3R_315() {
        if (jj_3R_258())
            return true;
        return jj_scan_token(85);
    }

    private static final boolean jj_3R_276() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_275();
    }

    private static final boolean jj_3R_473() {
        return jj_scan_token(103);
    }

    private static final boolean jj_3R_472() {
        return jj_scan_token(102);
    }

    private static final boolean jj_3R_273() {
        Token xsp = jj_scanpos;
        if (jj_3R_315()) {
            jj_scanpos = xsp;
            if (jj_3R_316()) {
                jj_scanpos = xsp;
                return jj_3R_317();
            }
        }
        return false;
    }

    private static final boolean jj_3R_465() {
        Token xsp = jj_scanpos;
        if (jj_3R_472()) {
            jj_scanpos = xsp;
            if (jj_3R_473())
                return true;
        }
        return jj_3R_458();
    }

    private static final boolean jj_3R_320() {
        if (jj_scan_token(30))
            return true;
        return jj_3R_337();
    }

    private static final boolean jj_3R_458() {
        Token xsp = jj_scanpos;
        if (jj_3R_465()) {
            jj_scanpos = xsp;
            if (jj_3R_466()) {
                jj_scanpos = xsp;
                if (jj_3R_467()) {
                    jj_scanpos = xsp;
                    return jj_3R_468();
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_105() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_104() {
        return jj_scan_token(53);
    }

    private static final boolean jj_3R_103() {
        return jj_scan_token(48);
    }

    private static final boolean jj_3R_102() {
        return jj_scan_token(49);
    }

    private static final boolean jj_3R_275() {
        if (jj_scan_token(76))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_320())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_101() {
        return jj_scan_token(50);
    }

    private static final boolean jj_3R_241() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_100() {
        return jj_scan_token(67);
    }

    private static final boolean jj_3R_238() {
        return jj_3R_273();
    }

    private static final boolean jj_3_13() {
        Token xsp = jj_scanpos;
        if (jj_3R_100()) {
            jj_scanpos = xsp;
            if (jj_3R_101()) {
                jj_scanpos = xsp;
                if (jj_3R_102()) {
                    jj_scanpos = xsp;
                    if (jj_3R_103()) {
                        jj_scanpos = xsp;
                        if (jj_3R_104()) {
                            jj_scanpos = xsp;
                            return jj_3R_105();
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_97() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3_13()) {
                jj_scanpos = xsp;
                if (jj_scan_token(29))
                    return true;
                if (jj_scan_token(76))
                    return true;
                xsp = jj_scanpos;
                if (jj_3R_153())
                    jj_scanpos = xsp;
                if (jj_scan_token(81))
                    return true;
                xsp = jj_scanpos;
                if (jj_3R_154())
                    jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_scan_token(86))
                    jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_155())
                    jj_scanpos = xsp;
                return jj_scan_token(82);
            }
        }
    }

    private static final boolean jj_3R_161() {
        if (jj_scan_token(81))
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_238()) {
                jj_scanpos = xsp;
                return jj_scan_token(82);
            }
        }
    }

    private static final boolean jj_3R_471() {
        return jj_scan_token(109);
    }

    private static final boolean jj_3R_470() {
        return jj_scan_token(105);
    }

    private static final boolean jj_3_12() {
        return jj_3R_99();
    }

    private static final boolean jj_3R_469() {
        return jj_scan_token(104);
    }

    private static final boolean jj_3R_425() {
        return jj_scan_token(66);
    }

    private static final boolean jj_3_11() {
        return jj_3R_98();
    }

    private static final boolean jj_3R_165() {
        if (jj_scan_token(89))
            return true;
        return jj_3R_240();
    }

    private static final boolean jj_3R_459() {
        Token xsp = jj_scanpos;
        if (jj_3R_469()) {
            jj_scanpos = xsp;
            if (jj_3R_470()) {
                jj_scanpos = xsp;
                if (jj_3R_471())
                    return true;
            }
        }
        return jj_3R_458();
    }

    private static final boolean jj_3_10() {
        return jj_3R_97();
    }

    private static final boolean jj_3R_451() {
        if (jj_3R_458())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_459()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3_9() {
        return jj_3R_96();
    }

    private static final boolean jj_3R_432() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_237() {
        return jj_3R_99();
    }

    private static final boolean jj_3_8() {
        return jj_3R_95();
    }

    private static final boolean jj_3R_236() {
        return jj_3R_98();
    }

    private static final boolean jj_3R_240() {
        if (jj_3R_275())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_276()) {
                jj_scanpos = xsp;
                return jj_scan_token(124);
            }
        }
    }

    private static final boolean jj_3R_235() {
        return jj_3R_97();
    }

    private static final boolean jj_3R_143() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_234() {
        return jj_3R_96();
    }

    private static final boolean jj_3R_424() {
        if (jj_scan_token(32))
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_432()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_233() {
        return jj_3R_95();
    }

    private static final boolean jj_3R_272() {
        if (jj_scan_token(25))
            return true;
        return jj_3R_137();
    }

    private static final boolean jj_3R_133() {
        if (jj_scan_token(76))
            return true;
        if (jj_scan_token(93))
            return true;
        return jj_3R_335();
    }

    private static final boolean jj_3R_131() {
        if (jj_scan_token(89))
            return true;
        if (jj_3R_188())
            return true;
        return jj_scan_token(124);
    }

    private static final boolean jj_3R_461() {
        return jj_scan_token(103);
    }

    private static final boolean jj_3R_460() {
        return jj_scan_token(102);
    }

    private static final boolean jj_3R_145() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_93() {
        Token xsp = jj_scanpos;
        if (jj_3R_145()) {
            jj_scanpos = xsp;
            if (jj_scan_token(50)) {
                jj_scanpos = xsp;
                return jj_scan_token(13);
            }
        }
        return false;
    }

    private static final boolean jj_3_7() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_93()) {
                jj_scanpos = xsp;
                if (jj_3R_94())
                    return true;
                return jj_scan_token(76);
            }
        }
    }

    private static final boolean jj_3R_452() {
        Token xsp = jj_scanpos;
        if (jj_3R_460()) {
            jj_scanpos = xsp;
            if (jj_3R_461())
                return true;
        }
        return jj_3R_451();
    }

    private static final boolean jj_3R_423() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_314() {
        return jj_scan_token(13);
    }

    private static final boolean jj_3R_313() {
        return jj_scan_token(50);
    }

    private static final boolean jj_3_62() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_137();
    }

    private static final boolean jj_3R_312() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_436() {
        if (jj_3R_451())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_452()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_271() {
        Token xsp = jj_scanpos;
        if (jj_3R_312()) {
            jj_scanpos = xsp;
            if (jj_3R_313()) {
                jj_scanpos = xsp;
                return jj_3R_314();
            }
        }
        return false;
    }

    private static final boolean jj_3R_415() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_423()) {
                jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_424())
                    jj_scanpos = xsp;
                if (jj_3R_94())
                    return true;
                xsp = jj_scanpos;
                if (jj_3R_425())
                    jj_scanpos = xsp;
                return jj_3R_206();
            }
        }
    }

    private static final boolean jj_3R_142() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_158() {
        Token xsp = jj_scanpos;
        if (jj_3R_232()) {
            jj_scanpos = xsp;
            if (jj_3R_233()) {
                jj_scanpos = xsp;
                if (jj_3R_234()) {
                    jj_scanpos = xsp;
                    if (jj_3R_235()) {
                        jj_scanpos = xsp;
                        if (jj_3R_236()) {
                            jj_scanpos = xsp;
                            if (jj_3R_237()) {
                                jj_scanpos = xsp;
                                return jj_scan_token(85);
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_232() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_271()) {
                jj_scanpos = xsp;
                if (jj_3R_94())
                    return true;
                if (jj_scan_token(76))
                    return true;
                if (jj_scan_token(79))
                    return true;
                if (jj_scan_token(80))
                    return true;
                xsp = jj_scanpos;
                if (jj_3R_272())
                    jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_373() {
        return jj_3R_412();
    }

    private static final boolean jj_3R_372() {
        return jj_3R_411();
    }

    private static final boolean jj_3R_371() {
        return jj_3R_410();
    }

    private static final boolean jj_3R_370() {
        return jj_3R_409();
    }

    private static final boolean jj_3R_369() {
        return jj_3R_408();
    }

    private static final boolean jj_3R_368() {
        return jj_3R_407();
    }

    private static final boolean jj_3R_260() {
        if (jj_3R_137())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3_62()) {
                jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_scan_token(86))
                    jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_367() {
        return jj_3R_406();
    }

    private static final boolean jj_3R_366() {
        return jj_3R_405();
    }

    private static final boolean jj_3R_388() {
        if (jj_3R_415())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_416()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_365() {
        return jj_3R_404();
    }

    private static final boolean jj_3R_364() {
        return jj_3R_403();
    }

    private static final boolean jj_3R_363() {
        return jj_3R_402();
    }

    private static final boolean jj_3R_195() {
        if (jj_scan_token(81))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_260())
            jj_scanpos = xsp;
        return jj_scan_token(82);
    }

    private static final boolean jj_3R_416() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_415();
    }

    private static final boolean jj_3R_362() {
        return jj_3R_401();
    }

    private static final boolean jj_3R_194() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_193() {
        return jj_3R_132();
    }

    private static final boolean jj_3_38() {
        return jj_3R_124();
    }

    private static final boolean jj_3_61() {
        return jj_3R_137();
    }

    private static final boolean jj_3R_140() {
        return jj_3R_144();
    }

    private static final boolean jj_3_37() {
        return jj_3R_123();
    }

    private static final boolean jj_3R_137() {
        Token xsp = jj_scanpos;
        if (jj_3R_193()) {
            jj_scanpos = xsp;
            if (jj_3R_194()) {
                jj_scanpos = xsp;
                return jj_3R_195();
            }
        }
        return false;
    }

    private static final boolean jj_3R_122() {
        return jj_scan_token(110);
    }

    private static final boolean jj_3R_361() {
        if (jj_3R_297())
            return true;
        return jj_scan_token(85);
    }

    private static final boolean jj_3R_350() {
        if (jj_scan_token(79))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_388())
            jj_scanpos = xsp;
        return jj_scan_token(80);
    }

    private static final boolean jj_3R_92() {
        return jj_3R_144();
    }

    private static final boolean jj_3_36() {
        Token xsp = jj_scanpos;
        if (jj_3R_122()) {
            jj_scanpos = xsp;
            if (jj_3_37()) {
                jj_scanpos = xsp;
                if (jj_3_38())
                    return true;
            }
        }
        return jj_3R_436();
    }

    private static final boolean jj_3R_360() {
        return jj_3R_400();
    }

    private static final boolean jj_3R_141() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_91() {
        return jj_scan_token(13);
    }

    private static final boolean jj_3R_359() {
        return jj_3R_161();
    }

    private static final boolean jj_3R_90() {
        return jj_scan_token(53);
    }

    private static final boolean jj_3R_434() {
        if (jj_3R_436())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3_36()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_319() {
        return jj_3R_137();
    }

    private static final boolean jj_3R_89() {
        return jj_scan_token(48);
    }

    private static final boolean jj_3R_88() {
        return jj_scan_token(49);
    }

    private static final boolean jj_3_54() {
        return jj_3R_133();
    }

    private static final boolean jj_3R_87() {
        return jj_scan_token(50);
    }

    private static final boolean jj_3R_336() {
        if (jj_scan_token(86))
            return true;
        if (jj_scan_token(76))
            return true;
        if (jj_scan_token(88))
            return true;
        return jj_3R_137();
    }

    private static final boolean jj_3R_86() {
        return jj_scan_token(67);
    }

    private static final boolean jj_3R_335() {
        Token xsp = jj_scanpos;
        if (jj_3_54()) {
            jj_scanpos = xsp;
            if (jj_3R_359()) {
                jj_scanpos = xsp;
                if (jj_3R_360()) {
                    jj_scanpos = xsp;
                    if (jj_3R_361()) {
                        jj_scanpos = xsp;
                        if (jj_3R_362()) {
                            jj_scanpos = xsp;
                            if (jj_3R_363()) {
                                jj_scanpos = xsp;
                                if (jj_3R_364()) {
                                    jj_scanpos = xsp;
                                    if (jj_3R_365()) {
                                        jj_scanpos = xsp;
                                        if (jj_3R_366()) {
                                            jj_scanpos = xsp;
                                            if (jj_3R_367()) {
                                                jj_scanpos = xsp;
                                                if (jj_3R_368()) {
                                                    jj_scanpos = xsp;
                                                    if (jj_3R_369()) {
                                                        jj_scanpos = xsp;
                                                        if (jj_3R_370()) {
                                                            jj_scanpos = xsp;
                                                            if (jj_3R_371()) {
                                                                jj_scanpos = xsp;
                                                                if (jj_3R_372()) {
                                                                    jj_scanpos = xsp;
                                                                    return jj_3R_373();
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3_6() {
        Token xsp = jj_scanpos;
        if (jj_3R_86()) {
            jj_scanpos = xsp;
            if (jj_3R_87()) {
                jj_scanpos = xsp;
                if (jj_3R_88()) {
                    jj_scanpos = xsp;
                    if (jj_3R_89()) {
                        jj_scanpos = xsp;
                        if (jj_3R_90()) {
                            jj_scanpos = xsp;
                            if (jj_3R_91()) {
                                jj_scanpos = xsp;
                                return jj_3R_92();
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_99() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3_6()) {
                jj_scanpos = xsp;
                if (jj_scan_token(15))
                    return true;
                if (jj_scan_token(42))
                    return true;
                if (jj_scan_token(76))
                    return true;
                if (jj_scan_token(81))
                    return true;
                while (true) {
                    xsp = jj_scanpos;
                    if (jj_3R_158()) {
                        jj_scanpos = xsp;
                        return jj_scan_token(82);
                    }
                }
                break;
            }
        }
    }

    private static final boolean jj_3R_399() {
        if (jj_scan_token(83))
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3R_440() {
        return jj_scan_token(96);
    }

    private static final boolean jj_3R_439() {
        return jj_scan_token(95);
    }

    private static final boolean jj_3R_438() {
        return jj_scan_token(124);
    }

    private static final boolean jj_3R_437() {
        return jj_scan_token(89);
    }

    private static final boolean jj_3_60() {
        if (jj_scan_token(76))
            return true;
        return jj_scan_token(88);
    }

    private static final boolean jj_3R_435() {
        Token xsp = jj_scanpos;
        if (jj_3R_437()) {
            jj_scanpos = xsp;
            if (jj_3R_438()) {
                jj_scanpos = xsp;
                if (jj_3R_439()) {
                    jj_scanpos = xsp;
                    if (jj_3R_440())
                        return true;
                }
            }
        }
        return jj_3R_434();
    }

    private static final boolean jj_3R_433() {
        if (jj_scan_token(83))
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3R_356() {
        if (jj_scan_token(76))
            return true;
        if (jj_3R_350())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_399()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_426() {
        if (jj_3R_433())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_433()) {
                jj_scanpos = xsp;
                return jj_3R_242();
            }
        }
    }

    private static final boolean jj_3R_428() {
        if (jj_3R_434())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_435()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3_52() {
        if (jj_scan_token(83))
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3R_85() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(67)) {
            jj_scanpos = xsp;
            if (jj_scan_token(50)) {
                jj_scanpos = xsp;
                if (jj_scan_token(49)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(48)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(53)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(13)) {
                                jj_scanpos = xsp;
                                return jj_3R_143();
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3_5() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_85()) {
                jj_scanpos = xsp;
                if (jj_scan_token(15))
                    return true;
                return jj_scan_token(42);
            }
        }
    }

    private static final boolean jj_3R_318() {
        if (jj_scan_token(76))
            return true;
        if (jj_scan_token(88))
            return true;
        if (jj_3R_137())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_336()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_274() {
        Token xsp = jj_scanpos;
        if (jj_3R_318()) {
            jj_scanpos = xsp;
            return jj_3R_319();
        }
        return false;
    }

    private static final boolean jj_3R_84() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(50)) {
            jj_scanpos = xsp;
            if (jj_scan_token(67)) {
                jj_scanpos = xsp;
                if (jj_scan_token(49)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(48)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(53)) {
                            jj_scanpos = xsp;
                            return jj_3R_142();
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3_4() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_84()) {
                jj_scanpos = xsp;
                return jj_scan_token(29);
            }
        }
    }

    private static final boolean jj_3R_83() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(13)) {
            jj_scanpos = xsp;
            if (jj_scan_token(50)) {
                jj_scanpos = xsp;
                if (jj_scan_token(67)) {
                    jj_scanpos = xsp;
                    return jj_3R_141();
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_166() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(50)) {
            jj_scanpos = xsp;
            if (jj_scan_token(49)) {
                jj_scanpos = xsp;
                if (jj_scan_token(48)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(53)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(13)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(32)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(44)) {
                                    jj_scanpos = xsp;
                                    if (jj_scan_token(56)) {
                                        jj_scanpos = xsp;
                                        if (jj_scan_token(67)) {
                                            jj_scanpos = xsp;
                                            return jj_3R_241();
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_167() {
        return jj_3R_165();
    }

    private static final boolean jj_3_3() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_83()) {
                jj_scanpos = xsp;
                return jj_scan_token(42);
            }
        }
    }

    private static final boolean jj_3R_113() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_166()) {
                jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_167())
                    jj_scanpos = xsp;
                if (jj_3R_129())
                    return true;
                if (jj_scan_token(76))
                    return true;
                return jj_scan_token(79);
            }
        }
    }

    private static final boolean jj_3R_82() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(13)) {
            jj_scanpos = xsp;
            if (jj_scan_token(32)) {
                jj_scanpos = xsp;
                if (jj_scan_token(50)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(67)) {
                        jj_scanpos = xsp;
                        return jj_3R_140();
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3_51() {
        if (jj_scan_token(83))
            return true;
        if (jj_3R_132())
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3_2() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_82()) {
                jj_scanpos = xsp;
                return jj_scan_token(22);
            }
        }
    }

    private static final boolean jj_3_53() {
        if (jj_3_51())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3_51()) {
                jj_scanpos = xsp;
                while (true) {
                    xsp = jj_scanpos;
                    if (jj_3_52()) {
                        jj_scanpos = xsp;
                        return false;
                    }
                }
                break;
            }
        }
    }

    private static final boolean jj_3R_417() {
        Token xsp = jj_scanpos;
        if (jj_3_53()) {
            jj_scanpos = xsp;
            return jj_3R_426();
        }
        return false;
    }

    private static final boolean jj_3R_429() {
        if (jj_scan_token(40))
            return true;
        return jj_3R_94();
    }

    private static final boolean jj_3R_421() {
        if (jj_3R_428())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_429())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_239() {
        if (jj_scan_token(79))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_274())
            jj_scanpos = xsp;
        return jj_scan_token(80);
    }

    private static final boolean jj_3R_144() {
        if (jj_scan_token(15))
            return true;
        if (jj_3R_94())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_239())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_358() {
        return jj_3R_161();
    }

    private static final boolean jj_3R_357() {
        if (jj_scan_token(59))
            return true;
        return jj_3R_188();
    }

    private static final boolean jj_3R_431() {
        return jj_scan_token(97);
    }

    private static final boolean jj_3R_420() {
        return jj_3R_417();
    }

    private static final boolean jj_3R_430() {
        return jj_scan_token(94);
    }

    private static final boolean jj_3R_422() {
        Token xsp = jj_scanpos;
        if (jj_3R_430()) {
            jj_scanpos = xsp;
            if (jj_3R_431())
                return true;
        }
        return jj_3R_421();
    }

    private static final boolean jj_3_59() {
        return jj_3R_117();
    }

    private static final boolean jj_3R_413() {
        if (jj_3R_421())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_422()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_355() {
        if (jj_scan_token(89))
            return true;
        return jj_3R_240();
    }

    private static final boolean jj_3R_427() {
        return jj_3R_219();
    }

    private static final boolean jj_3R_419() {
        if (jj_3R_119())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_427())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_398() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_418() {
        return jj_3R_131();
    }

    private static final boolean jj_3R_397() {
        return jj_scan_token(67);
    }

    private static final boolean jj_3R_396() {
        return jj_scan_token(56);
    }

    private static final boolean jj_3R_395() {
        return jj_scan_token(44);
    }

    private static final boolean jj_3R_394() {
        return jj_scan_token(13);
    }

    private static final boolean jj_3R_393() {
        return jj_scan_token(32);
    }

    private static final boolean jj_3R_414() {
        if (jj_scan_token(106))
            return true;
        return jj_3R_413();
    }

    private static final boolean jj_3R_392() {
        return jj_scan_token(53);
    }

    private static final boolean jj_3R_391() {
        return jj_scan_token(48);
    }

    private static final boolean jj_3R_390() {
        return jj_scan_token(49);
    }

    private static final boolean jj_3R_187() {
        if (jj_scan_token(45))
            return true;
        if (jj_3R_120())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_418())
            jj_scanpos = xsp;
        xsp = jj_scanpos;
        if (jj_3R_419()) {
            jj_scanpos = xsp;
            return jj_3R_420();
        }
        return false;
    }

    private static final boolean jj_3R_389() {
        return jj_scan_token(50);
    }

    private static final boolean jj_3R_379() {
        if (jj_3R_413())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_414()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_354() {
        Token xsp = jj_scanpos;
        if (jj_3R_389()) {
            jj_scanpos = xsp;
            if (jj_3R_390()) {
                jj_scanpos = xsp;
                if (jj_3R_391()) {
                    jj_scanpos = xsp;
                    if (jj_3R_392()) {
                        jj_scanpos = xsp;
                        if (jj_3R_393()) {
                            jj_scanpos = xsp;
                            if (jj_3R_394()) {
                                jj_scanpos = xsp;
                                if (jj_3R_395()) {
                                    jj_scanpos = xsp;
                                    if (jj_3R_396()) {
                                        jj_scanpos = xsp;
                                        if (jj_3R_397()) {
                                            jj_scanpos = xsp;
                                            return jj_3R_398();
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_334() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_354()) {
                jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_355())
                    jj_scanpos = xsp;
                if (jj_3R_129())
                    return true;
                if (jj_3R_356())
                    return true;
                xsp = jj_scanpos;
                if (jj_3R_357())
                    jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_358()) {
                    jj_scanpos = xsp;
                    return jj_scan_token(85);
                }
                return false;
            }
        }
    }

    private static final boolean jj_3_50() {
        if (jj_scan_token(45))
            return true;
        if (jj_3R_126())
            return true;
        return jj_3R_417();
    }

    private static final boolean jj_3R_130() {
        Token xsp = jj_scanpos;
        if (jj_3_50()) {
            jj_scanpos = xsp;
            return jj_3R_187();
        }
        return false;
    }

    private static final boolean jj_3R_449() {
        if (jj_scan_token(33))
            return true;
        return jj_3R_161();
    }

    private static final boolean jj_3_49() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_132();
    }

    private static final boolean jj_3R_380() {
        if (jj_scan_token(108))
            return true;
        return jj_3R_379();
    }

    private static final boolean jj_3R_138() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_81() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_138()) {
                jj_scanpos = xsp;
                if (jj_scan_token(47))
                    return true;
                if (jj_3R_139())
                    return true;
                return jj_scan_token(85);
            }
        }
    }

    private static final boolean jj_3R_341() {
        if (jj_3R_379())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_380()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_250() {
        if (jj_3R_132())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_278()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3_27() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_116();
    }

    private static final boolean jj_3R_278() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_132();
    }

    private static final boolean jj_3R_448() {
        if (jj_scan_token(20))
            return true;
        if (jj_scan_token(79))
            return true;
        if (jj_3R_415())
            return true;
        if (jj_scan_token(80))
            return true;
        return jj_3R_161();
    }

    private static final boolean jj_3R_346() {
        if (jj_3R_116())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3_27()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_242() {
        if (jj_scan_token(81))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_346())
            jj_scanpos = xsp;
        xsp = jj_scanpos;
        if (jj_scan_token(86))
            jj_scanpos = xsp;
        return jj_scan_token(82);
    }

    private static final boolean jj_3R_175() {
        return jj_3R_250();
    }

    private static final boolean jj_3R_411() {
        if (jj_scan_token(62))
            return true;
        if (jj_3R_161())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_448()) {
                jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_449())
                    jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_119() {
        if (jj_scan_token(79))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_175())
            jj_scanpos = xsp;
        return jj_scan_token(80);
    }

    private static final boolean jj_3R_342() {
        if (jj_scan_token(107))
            return true;
        return jj_3R_341();
    }

    private static final boolean jj_3R_327() {
        if (jj_3R_341())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_342()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3_1() {
        return jj_3R_81();
    }

    private static final boolean jj_3R_171() {
        return jj_3R_132();
    }

    private static final boolean jj_3R_170() {
        return jj_3R_242();
    }

    private static final boolean jj_3R_116() {
        Token xsp = jj_scanpos;
        if (jj_3R_170()) {
            jj_scanpos = xsp;
            return jj_3R_171();
        }
        return false;
    }

    private static final boolean jj_3R_339() {
        return jj_scan_token(46);
    }

    private static final boolean jj_3R_264() {
        if (jj_scan_token(83))
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3R_410() {
        if (jj_scan_token(56))
            return true;
        if (jj_scan_token(79))
            return true;
        if (jj_3R_132())
            return true;
        if (jj_scan_token(80))
            return true;
        return jj_3R_161();
    }

    private static final boolean jj_3R_328() {
        if (jj_scan_token(99))
            return true;
        return jj_3R_327();
    }

    private static final boolean jj_3R_376() {
        return jj_scan_token(31);
    }

    private static final boolean jj_3R_280() {
        if (jj_3R_327())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_328()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_375() {
        return jj_scan_token(61);
    }

    private static final boolean jj_3R_206() {
        if (jj_scan_token(76))
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_264()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_338() {
        Token xsp = jj_scanpos;
        if (jj_3R_375()) {
            jj_scanpos = xsp;
            return jj_3R_376();
        }
        return false;
    }

    private static final boolean jj_3R_169() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_168() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_326() {
        return jj_3R_339();
    }

    private static final boolean jj_3R_207() {
        if (jj_scan_token(88))
            return true;
        return jj_3R_116();
    }

    private static final boolean jj_3R_409() {
        if (jj_scan_token(58))
            return true;
        if (jj_3R_132())
            return true;
        return jj_scan_token(85);
    }

    private static final boolean jj_3R_325() {
        return jj_3R_338();
    }

    private static final boolean jj_3R_149() {
        if (jj_3R_206())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_207())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_281() {
        if (jj_scan_token(98))
            return true;
        return jj_3R_280();
    }

    private static final boolean jj_3R_324() {
        return jj_scan_token(75);
    }

    private static final boolean jj_3R_255() {
        if (jj_3R_280())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_281()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_323() {
        return jj_scan_token(74);
    }

    private static final boolean jj_3R_447() {
        return jj_3R_132();
    }

    private static final boolean jj_3R_322() {
        return jj_scan_token(72);
    }

    private static final boolean jj_3R_408() {
        if (jj_scan_token(51))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_447())
            jj_scanpos = xsp;
        return jj_scan_token(85);
    }

    private static final boolean jj_3R_150() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_149();
    }

    private static final boolean jj_3R_321() {
        return jj_scan_token(68);
    }

    private static final boolean jj_3R_256() {
        if (jj_scan_token(92))
            return true;
        if (jj_3R_132())
            return true;
        if (jj_scan_token(93))
            return true;
        return jj_3R_189();
    }

    private static final boolean jj_3R_277() {
        Token xsp = jj_scanpos;
        if (jj_3R_321()) {
            jj_scanpos = xsp;
            if (jj_3R_322()) {
                jj_scanpos = xsp;
                if (jj_3R_323()) {
                    jj_scanpos = xsp;
                    if (jj_3R_324()) {
                        jj_scanpos = xsp;
                        if (jj_3R_325()) {
                            jj_scanpos = xsp;
                            return jj_3R_326();
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_189() {
        if (jj_3R_255())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_256())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_446() {
        return jj_scan_token(76);
    }

    private static final boolean jj_3R_184() {
        return jj_3R_119();
    }

    private static final boolean jj_3R_293() {
        return jj_scan_token(116);
    }

    private static final boolean jj_3R_292() {
        return jj_scan_token(117);
    }

    private static final boolean jj_3R_205() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_291() {
        return jj_scan_token(115);
    }

    private static final boolean jj_3R_407() {
        if (jj_scan_token(24))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_446())
            jj_scanpos = xsp;
        return jj_scan_token(85);
    }

    private static final boolean jj_3R_204() {
        return jj_scan_token(64);
    }

    private static final boolean jj_3R_290() {
        return jj_scan_token(121);
    }

    private static final boolean jj_3R_203() {
        return jj_scan_token(60);
    }

    private static final boolean jj_3R_289() {
        return jj_scan_token(120);
    }

    private static final boolean jj_3R_202() {
        return jj_scan_token(32);
    }

    private static final boolean jj_3R_288() {
        return jj_scan_token(119);
    }

    private static final boolean jj_3R_201() {
        return jj_scan_token(53);
    }

    private static final boolean jj_3R_287() {
        return jj_scan_token(112);
    }

    private static final boolean jj_3R_200() {
        return jj_scan_token(48);
    }

    private static final boolean jj_3R_286() {
        return jj_scan_token(111);
    }

    private static final boolean jj_3R_183() {
        if (jj_scan_token(87))
            return true;
        return jj_scan_token(76);
    }

    private static final boolean jj_3R_199() {
        return jj_scan_token(49);
    }

    private static final boolean jj_3R_285() {
        return jj_scan_token(118);
    }

    private static final boolean jj_3R_198() {
        return jj_scan_token(50);
    }

    private static final boolean jj_3R_284() {
        return jj_scan_token(114);
    }

    private static final boolean jj_3R_283() {
        return jj_scan_token(113);
    }

    private static final boolean jj_3R_282() {
        return jj_scan_token(88);
    }

    private static final boolean jj_3R_148() {
        Token xsp = jj_scanpos;
        if (jj_3R_198()) {
            jj_scanpos = xsp;
            if (jj_3R_199()) {
                jj_scanpos = xsp;
                if (jj_3R_200()) {
                    jj_scanpos = xsp;
                    if (jj_3R_201()) {
                        jj_scanpos = xsp;
                        if (jj_3R_202()) {
                            jj_scanpos = xsp;
                            if (jj_3R_203()) {
                                jj_scanpos = xsp;
                                if (jj_3R_204()) {
                                    jj_scanpos = xsp;
                                    return jj_3R_205();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_182() {
        if (jj_scan_token(83))
            return true;
        if (jj_3R_132())
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3R_257() {
        Token xsp = jj_scanpos;
        if (jj_3R_282()) {
            jj_scanpos = xsp;
            if (jj_3R_283()) {
                jj_scanpos = xsp;
                if (jj_3R_284()) {
                    jj_scanpos = xsp;
                    if (jj_3R_285()) {
                        jj_scanpos = xsp;
                        if (jj_3R_286()) {
                            jj_scanpos = xsp;
                            if (jj_3R_287()) {
                                jj_scanpos = xsp;
                                if (jj_3R_288()) {
                                    jj_scanpos = xsp;
                                    if (jj_3R_289()) {
                                        jj_scanpos = xsp;
                                        if (jj_3R_290()) {
                                            jj_scanpos = xsp;
                                            if (jj_3R_291()) {
                                                jj_scanpos = xsp;
                                                if (jj_3R_292()) {
                                                    jj_scanpos = xsp;
                                                    return jj_3R_293();
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_95() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_148()) {
                jj_scanpos = xsp;
                if (jj_3R_94())
                    return true;
                if (jj_3R_149())
                    return true;
                while (true) {
                    xsp = jj_scanpos;
                    if (jj_3R_150()) {
                        jj_scanpos = xsp;
                        return jj_scan_token(85);
                    }
                }
                break;
            }
        }
    }

    private static final boolean jj_3R_445() {
        return jj_scan_token(76);
    }

    private static final boolean jj_3_48() {
        if (jj_scan_token(87))
            return true;
        if (jj_3R_131())
            return true;
        return jj_scan_token(76);
    }

    private static final boolean jj_3R_406() {
        if (jj_scan_token(17))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_445())
            jj_scanpos = xsp;
        return jj_scan_token(85);
    }

    private static final boolean jj_3_26() {
        return jj_3R_99();
    }

    private static final boolean jj_3_47() {
        if (jj_scan_token(87))
            return true;
        return jj_3R_130();
    }

    private static final boolean jj_3_25() {
        return jj_3R_97();
    }

    private static final boolean jj_3R_115() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(53)) {
            jj_scanpos = xsp;
            if (jj_scan_token(13)) {
                jj_scanpos = xsp;
                if (jj_scan_token(32)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(50)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(49)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(48)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(67)) {
                                    jj_scanpos = xsp;
                                    return jj_3R_169();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3_24() {
        return jj_3R_113();
    }

    private static final boolean jj_3R_190() {
        if (jj_3R_257())
            return true;
        return jj_3R_132();
    }

    private static final boolean jj_3R_114() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(53)) {
            jj_scanpos = xsp;
            if (jj_scan_token(13)) {
                jj_scanpos = xsp;
                if (jj_scan_token(32)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(50)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(49)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(48)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(67)) {
                                    jj_scanpos = xsp;
                                    return jj_3R_168();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3_23() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_115()) {
                jj_scanpos = xsp;
                return jj_scan_token(42);
            }
        }
    }

    private static final boolean jj_3_46() {
        if (jj_scan_token(87))
            return true;
        return jj_scan_token(54);
    }

    private static final boolean jj_3_22() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_114()) {
                jj_scanpos = xsp;
                return jj_scan_token(22);
            }
        }
    }

    private static final boolean jj_3R_464() {
        return jj_3R_259();
    }

    private static final boolean jj_3R_311() {
        if (jj_3R_95())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_132() {
        if (jj_3R_189())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_190())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_310() {
        if (jj_3R_99())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3_45() {
        if (jj_scan_token(87))
            return true;
        return jj_scan_token(57);
    }

    private static final boolean jj_3R_309() {
        if (jj_3R_97())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_308() {
        if (jj_3R_334())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_128() {
        Token xsp = jj_scanpos;
        if (jj_3_45()) {
            jj_scanpos = xsp;
            lookingAhead = true;
            jj_semLA = isSuperAllowed();
            lookingAhead = false;
            if (!jj_semLA || jj_3_46()) {
                jj_scanpos = xsp;
                if (jj_3_47()) {
                    jj_scanpos = xsp;
                    if (jj_3_48()) {
                        jj_scanpos = xsp;
                        if (jj_3R_182()) {
                            jj_scanpos = xsp;
                            if (jj_3R_183()) {
                                jj_scanpos = xsp;
                                return jj_3R_184();
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_259() {
        if (jj_3R_297())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_298()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_307() {
        if (jj_3R_98())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_298() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_297();
    }

    private static final boolean jj_3R_306() {
        if (jj_3R_96())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_270() {
        Token xsp = jj_scanpos;
        if (jj_3R_306()) {
            jj_scanpos = xsp;
            if (jj_3R_307()) {
                jj_scanpos = xsp;
                if (jj_3R_308()) {
                    jj_scanpos = xsp;
                    if (jj_3R_309()) {
                        jj_scanpos = xsp;
                        if (jj_3R_310()) {
                            jj_scanpos = xsp;
                            return jj_3R_311();
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3_44() {
        if (jj_3R_129())
            return true;
        if (jj_scan_token(87))
            return true;
        return jj_scan_token(22);
    }

    private static final boolean jj_3_58() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(32))
            jj_scanpos = xsp;
        if (jj_3R_94())
            return true;
        return jj_scan_token(76);
    }

    private static final boolean jj_3R_249() {
        return jj_3R_139();
    }

    private static final boolean jj_3R_231() {
        return jj_3R_270();
    }

    private static final boolean jj_3R_266() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_120();
    }

    private static final boolean jj_3R_248() {
        if (jj_3R_129())
            return true;
        if (jj_scan_token(87))
            return true;
        return jj_scan_token(22);
    }

    private static final boolean jj_3R_192() {
        return jj_3R_259();
    }

    private static final boolean jj_3R_191() {
        return jj_3R_258();
    }

    private static final boolean jj_3R_188() {
        if (jj_3R_120())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_266()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_247() {
        return jj_3R_130();
    }

    private static final boolean jj_3R_136() {
        Token xsp = jj_scanpos;
        if (jj_3R_191()) {
            jj_scanpos = xsp;
            return jj_3R_192();
        }
        return false;
    }

    private static final boolean jj_3R_230() {
        if (jj_scan_token(30))
            return true;
        return jj_3R_188();
    }

    private static final boolean jj_3R_279() {
        if (jj_scan_token(86))
            return true;
        return jj_3R_176();
    }

    private static final boolean jj_3R_246() {
        if (jj_scan_token(79))
            return true;
        if (jj_3R_132())
            return true;
        return jj_scan_token(80);
    }

    private static final boolean jj_3R_229() {
        return jj_3R_165();
    }

    private static final boolean jj_3R_135() {
        return jj_3R_136();
    }

    private static final boolean jj_3_57() {
        if (jj_scan_token(79))
            return true;
        if (jj_3R_136())
            return true;
        return jj_scan_token(93);
    }

    private static final boolean jj_3R_455() {
        return jj_3R_136();
    }

    private static final boolean jj_3R_456() {
        return jj_3R_132();
    }

    private static final boolean jj_3_56() {
        if (jj_scan_token(79))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_135())
            jj_scanpos = xsp;
        return jj_scan_token(85);
    }

    private static final boolean jj_3R_163() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_457() {
        return jj_3R_464();
    }

    private static final boolean jj_3R_378() {
        return jj_scan_token(54);
    }

    private static final boolean jj_3R_162() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_377() {
        return jj_scan_token(30);
    }

    private static final boolean jj_3R_112() {
        return jj_3R_165();
    }

    private static final boolean jj_3R_444() {
        if (jj_scan_token(79))
            return true;
        if (jj_3R_136())
            return true;
        if (jj_scan_token(93))
            return true;
        return jj_3R_132();
    }

    private static final boolean jj_3R_340() {
        Token xsp = jj_scanpos;
        if (jj_3R_377()) {
            jj_scanpos = xsp;
            if (jj_3R_378())
                return true;
        }
        return jj_3R_94();
    }

    private static final boolean jj_3R_157() {
        if (jj_scan_token(42))
            return true;
        if (jj_scan_token(76))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_229())
            jj_scanpos = xsp;
        xsp = jj_scanpos;
        if (jj_3R_230())
            jj_scanpos = xsp;
        if (jj_scan_token(81))
            return true;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_231()) {
                jj_scanpos = xsp;
                return jj_scan_token(82);
            }
        }
    }

    private static final boolean jj_3R_245() {
        if (jj_scan_token(54))
            return true;
        if (jj_scan_token(87))
            return true;
        return jj_scan_token(76);
    }

    private static final boolean jj_3R_443() {
        if (jj_scan_token(79))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_455())
            jj_scanpos = xsp;
        if (jj_scan_token(85))
            return true;
        xsp = jj_scanpos;
        if (jj_3R_456())
            jj_scanpos = xsp;
        if (jj_scan_token(85))
            return true;
        xsp = jj_scanpos;
        if (jj_3R_457())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_244() {
        return jj_scan_token(57);
    }

    private static final boolean jj_3R_252() {
        if (jj_scan_token(92))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_340())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_251() {
        return jj_3R_94();
    }

    private static final boolean jj_3R_243() {
        return jj_3R_277();
    }

    private static final boolean jj_3R_164() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_405() {
        if (jj_scan_token(35))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_443()) {
            jj_scanpos = xsp;
            if (jj_3R_444())
                return true;
        }
        if (jj_scan_token(80))
            return true;
        return jj_3R_335();
    }

    private static final boolean jj_3R_176() {
        Token xsp = jj_scanpos;
        if (jj_3R_251()) {
            jj_scanpos = xsp;
            return jj_3R_252();
        }
        return false;
    }

    private static final boolean jj_3R_228() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_174() {
        Token xsp = jj_scanpos;
        if (jj_3R_243()) {
            jj_scanpos = xsp;
            if (jj_3R_244()) {
                jj_scanpos = xsp;
                if (jj_3R_245()) {
                    jj_scanpos = xsp;
                    if (jj_3R_246()) {
                        jj_scanpos = xsp;
                        if (jj_3R_247()) {
                            jj_scanpos = xsp;
                            if (jj_3R_248()) {
                                jj_scanpos = xsp;
                                return jj_3R_249();
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_227() {
        return jj_scan_token(67);
    }

    private static final boolean jj_3R_226() {
        return jj_scan_token(48);
    }

    private static final boolean jj_3R_121() {
        if (jj_scan_token(89))
            return true;
        if (jj_3R_176())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_279()) {
                jj_scanpos = xsp;
                return jj_scan_token(124);
            }
        }
    }

    private static final boolean jj_3R_225() {
        return jj_scan_token(49);
    }

    private static final boolean jj_3R_224() {
        return jj_scan_token(50);
    }

    private static final boolean jj_3R_223() {
        return jj_scan_token(32);
    }

    private static final boolean jj_3R_222() {
        return jj_scan_token(13);
    }

    private static final boolean jj_3R_221() {
        return jj_scan_token(53);
    }

    private static final boolean jj_3R_156() {
        Token xsp = jj_scanpos;
        if (jj_3R_221()) {
            jj_scanpos = xsp;
            if (jj_3R_222()) {
                jj_scanpos = xsp;
                if (jj_3R_223()) {
                    jj_scanpos = xsp;
                    if (jj_3R_224()) {
                        jj_scanpos = xsp;
                        if (jj_3R_225()) {
                            jj_scanpos = xsp;
                            if (jj_3R_226()) {
                                jj_scanpos = xsp;
                                if (jj_3R_227()) {
                                    jj_scanpos = xsp;
                                    return jj_3R_228();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_98() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_156()) {
                jj_scanpos = xsp;
                return jj_3R_157();
            }
        }
    }

    private static final boolean jj_3R_404() {
        if (jj_scan_token(26))
            return true;
        if (jj_3R_335())
            return true;
        if (jj_scan_token(65))
            return true;
        if (jj_scan_token(79))
            return true;
        if (jj_3R_132())
            return true;
        if (jj_scan_token(80))
            return true;
        return jj_scan_token(85);
    }

    private static final boolean jj_3_35() {
        return jj_3R_121();
    }

    private static final boolean jj_3_34() {
        if (jj_scan_token(87))
            return true;
        if (jj_scan_token(76))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3_35())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_111() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(50)) {
            jj_scanpos = xsp;
            if (jj_scan_token(49)) {
                jj_scanpos = xsp;
                if (jj_scan_token(48))
                    return true;
            }
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_164()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3_33() {
        return jj_3R_121();
    }

    private static final boolean jj_3R_403() {
        if (jj_scan_token(65))
            return true;
        if (jj_scan_token(79))
            return true;
        if (jj_3R_132())
            return true;
        if (jj_scan_token(80))
            return true;
        return jj_3R_335();
    }

    private static final boolean jj_3R_120() {
        if (jj_scan_token(76))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3_33())
            jj_scanpos = xsp;
        while (true) {
            xsp = jj_scanpos;
            if (jj_3_34()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3_21() {
        return jj_3R_99();
    }

    private static final boolean jj_3_20() {
        return jj_3R_97();
    }

    private static final boolean jj_3_19() {
        return jj_3R_113();
    }

    private static final boolean jj_3R_110() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_109() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(53)) {
            jj_scanpos = xsp;
            if (jj_scan_token(13)) {
                jj_scanpos = xsp;
                if (jj_scan_token(32)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(50)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(49)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(48)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(67)) {
                                    jj_scanpos = xsp;
                                    return jj_3R_163();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3_18() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_110()) {
                jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_111())
                    jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_112())
                    jj_scanpos = xsp;
                if (jj_scan_token(76))
                    return true;
                return jj_scan_token(79);
            }
        }
    }

    private static final boolean jj_3R_108() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(53)) {
            jj_scanpos = xsp;
            if (jj_scan_token(13)) {
                jj_scanpos = xsp;
                if (jj_scan_token(32)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(50)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(49)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(48)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(67)) {
                                    jj_scanpos = xsp;
                                    return jj_3R_162();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3_17() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_109()) {
                jj_scanpos = xsp;
                return jj_scan_token(42);
            }
        }
    }

    private static final boolean jj_3R_305() {
        if (jj_3R_95())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3_16() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_108()) {
                jj_scanpos = xsp;
                return jj_scan_token(22);
            }
        }
    }

    private static final boolean jj_3R_304() {
        if (jj_3R_99())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_303() {
        if (jj_3R_97())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_302() {
        if (jj_3R_334())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_301() {
        if (jj_3R_333())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3_32() {
        if (jj_scan_token(87))
            return true;
        return jj_scan_token(76);
    }

    private static final boolean jj_3R_442() {
        if (jj_scan_token(28))
            return true;
        return jj_3R_335();
    }

    private static final boolean jj_3R_300() {
        if (jj_3R_98())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_299() {
        if (jj_3R_96())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3_15() {
        if (jj_3R_107())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_scan_token(85)) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_269() {
        Token xsp = jj_scanpos;
        if (jj_3_15()) {
            jj_scanpos = xsp;
            if (jj_3R_299()) {
                jj_scanpos = xsp;
                if (jj_3R_300()) {
                    jj_scanpos = xsp;
                    if (jj_3R_301()) {
                        jj_scanpos = xsp;
                        if (jj_3R_302()) {
                            jj_scanpos = xsp;
                            if (jj_3R_303()) {
                                jj_scanpos = xsp;
                                if (jj_3R_304()) {
                                    jj_scanpos = xsp;
                                    return jj_3R_305();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_139() {
        if (jj_scan_token(76))
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3_32()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_402() {
        if (jj_scan_token(37))
            return true;
        if (jj_scan_token(79))
            return true;
        if (jj_3R_132())
            return true;
        if (jj_scan_token(80))
            return true;
        if (jj_3R_335())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_442())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_215() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_214() {
        return jj_scan_token(67);
    }

    private static final boolean jj_3R_213() {
        return jj_scan_token(48);
    }

    private static final boolean jj_3R_186() {
        return jj_3R_94();
    }

    private static final boolean jj_3R_212() {
        return jj_scan_token(49);
    }

    private static final boolean jj_3R_211() {
        return jj_scan_token(50);
    }

    private static final boolean jj_3R_210() {
        return jj_scan_token(32);
    }

    private static final boolean jj_3R_209() {
        return jj_scan_token(13);
    }

    private static final boolean jj_3R_208() {
        return jj_scan_token(53);
    }

    private static final boolean jj_3R_151() {
        Token xsp = jj_scanpos;
        if (jj_3R_208()) {
            jj_scanpos = xsp;
            if (jj_3R_209()) {
                jj_scanpos = xsp;
                if (jj_3R_210()) {
                    jj_scanpos = xsp;
                    if (jj_3R_211()) {
                        jj_scanpos = xsp;
                        if (jj_3R_212()) {
                            jj_scanpos = xsp;
                            if (jj_3R_213()) {
                                jj_scanpos = xsp;
                                if (jj_3R_214()) {
                                    jj_scanpos = xsp;
                                    return jj_3R_215();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_185() {
        return jj_scan_token(63);
    }

    private static final boolean jj_3R_96() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_151()) {
                jj_scanpos = xsp;
                return jj_3R_152();
            }
        }
    }

    private static final boolean jj_3R_129() {
        Token xsp = jj_scanpos;
        if (jj_3R_185()) {
            jj_scanpos = xsp;
            return jj_3R_186();
        }
        return false;
    }

    private static final boolean jj_3R_450() {
        if (jj_scan_token(93))
            return true;
        return jj_3R_132();
    }

    private static final boolean jj_3R_412() {
        if (jj_scan_token(14))
            return true;
        if (jj_3R_132())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_450())
            jj_scanpos = xsp;
        return jj_scan_token(85);
    }

    private static final boolean jj_3R_265() {
        return jj_3R_269();
    }

    private static final boolean jj_3R_219() {
        if (jj_scan_token(81))
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_265()) {
                jj_scanpos = xsp;
                return jj_scan_token(82);
            }
        }
    }

    private static final boolean jj_3_43() {
        return jj_3R_128();
    }

    private static final boolean jj_3R_126() {
        Token xsp = jj_scanpos;
        if (jj_scan_token(16)) {
            jj_scanpos = xsp;
            if (jj_scan_token(21)) {
                jj_scanpos = xsp;
                if (jj_scan_token(18)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(52)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(41)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(43)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(34)) {
                                    jj_scanpos = xsp;
                                    return jj_scan_token(27);
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_263() {
        if (jj_scan_token(83))
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3R_463() {
        if (jj_scan_token(25))
            return true;
        return jj_scan_token(93);
    }

    private static final boolean jj_3R_254() {
        return jj_3R_277();
    }

    private static final boolean jj_3R_262() {
        return jj_3R_139();
    }

    private static final boolean jj_3R_261() {
        return jj_3R_126();
    }

    private static final boolean jj_3R_197() {
        Token xsp = jj_scanpos;
        if (jj_3R_261()) {
            jj_scanpos = xsp;
            if (jj_3R_262())
                return true;
        }
        while (true) {
            xsp = jj_scanpos;
            if (jj_3R_263()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_218() {
        if (jj_scan_token(38))
            return true;
        return jj_3R_188();
    }

    private static final boolean jj_3R_462() {
        if (jj_scan_token(19))
            return true;
        if (jj_3R_132())
            return true;
        return jj_scan_token(93);
    }

    private static final boolean jj_3R_147() {
        return jj_3R_197();
    }

    private static final boolean jj_3R_453() {
        Token xsp = jj_scanpos;
        if (jj_3R_462()) {
            jj_scanpos = xsp;
            return jj_3R_463();
        }
        return false;
    }

    private static final boolean jj_3_31() {
        return jj_3R_120();
    }

    private static final boolean jj_3R_196() {
        if (jj_scan_token(83))
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3R_118() {
        if (jj_3R_174())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3_43()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_217() {
        if (jj_scan_token(30))
            return true;
        return jj_3R_120();
    }

    private static final boolean jj_3R_146() {
        if (jj_3R_120())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_196()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_216() {
        return jj_3R_165();
    }

    private static final boolean jj_3R_94() {
        Token xsp = jj_scanpos;
        if (jj_3R_146()) {
            jj_scanpos = xsp;
            return jj_3R_147();
        }
        return false;
    }

    private static final boolean jj_3_42() {
        if (jj_scan_token(79))
            return true;
        return jj_3R_126();
    }

    private static final boolean jj_3R_454() {
        return jj_3R_273();
    }

    private static final boolean jj_3R_152() {
        if (jj_scan_token(22))
            return true;
        if (jj_scan_token(76))
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_216())
            jj_scanpos = xsp;
        xsp = jj_scanpos;
        if (jj_3R_217())
            jj_scanpos = xsp;
        xsp = jj_scanpos;
        if (jj_3R_218())
            jj_scanpos = xsp;
        return jj_3R_219();
    }

    private static final boolean jj_3R_483() {
        if (jj_scan_token(79))
            return true;
        if (jj_3R_94())
            return true;
        if (jj_scan_token(80))
            return true;
        return jj_3R_474();
    }

    private static final boolean jj_3R_482() {
        if (jj_scan_token(79))
            return true;
        if (jj_3R_94())
            return true;
        if (jj_scan_token(80))
            return true;
        return jj_3R_458();
    }

    private static final boolean jj_3R_441() {
        if (jj_3R_453())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_454()) {
                jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_480() {
        Token xsp = jj_scanpos;
        if (jj_3R_482()) {
            jj_scanpos = xsp;
            return jj_3R_483();
        }
        return false;
    }

    private static final boolean jj_3R_401() {
        if (jj_scan_token(55))
            return true;
        if (jj_scan_token(79))
            return true;
        if (jj_3R_132())
            return true;
        if (jj_scan_token(80))
            return true;
        if (jj_scan_token(81))
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_441()) {
                jj_scanpos = xsp;
                return jj_scan_token(82);
            }
        }
    }

    private static final boolean jj_3R_127() {
        if (jj_scan_token(83))
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3R_160() {
        return jj_scan_token(53);
    }

    private static final boolean jj_3R_486() {
        return jj_scan_token(101);
    }

    private static final boolean jj_3R_107() {
        Token xsp = jj_scanpos;
        if (jj_3R_160())
            jj_scanpos = xsp;
        return jj_3R_161();
    }

    private static final boolean jj_3R_253() {
        if (jj_scan_token(83))
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3R_485() {
        return jj_scan_token(100);
    }

    private static final boolean jj_3R_484() {
        Token xsp = jj_scanpos;
        if (jj_3R_485()) {
            jj_scanpos = xsp;
            return jj_3R_486();
        }
        return false;
    }

    private static final boolean jj_3R_481() {
        if (jj_3R_118())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_484())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3_41() {
        if (jj_scan_token(79))
            return true;
        if (jj_3R_120())
            return true;
        return jj_scan_token(83);
    }

    private static final boolean jj_3R_383() {
        if (jj_3R_257())
            return true;
        return jj_3R_132();
    }

    private static final boolean jj_3_40() {
        if (jj_scan_token(79))
            return true;
        if (jj_3R_126())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_127()) {
                jj_scanpos = xsp;
                return jj_scan_token(80);
            }
        }
    }

    private static final boolean jj_3R_181() {
        if (jj_scan_token(79))
            return true;
        if (jj_3R_120())
            return true;
        if (jj_scan_token(80))
            return true;
        Token xsp = jj_scanpos;
        if (jj_scan_token(91)) {
            jj_scanpos = xsp;
            if (jj_scan_token(90)) {
                jj_scanpos = xsp;
                if (jj_scan_token(79)) {
                    jj_scanpos = xsp;
                    if (jj_scan_token(76)) {
                        jj_scanpos = xsp;
                        if (jj_scan_token(57)) {
                            jj_scanpos = xsp;
                            if (jj_scan_token(54)) {
                                jj_scanpos = xsp;
                                if (jj_scan_token(45)) {
                                    jj_scanpos = xsp;
                                    return jj_3R_254();
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    private static final boolean jj_3R_382() {
        return jj_scan_token(101);
    }

    private static final boolean jj_3R_180() {
        if (jj_scan_token(79))
            return true;
        if (jj_3R_120())
            return true;
        if (jj_scan_token(83))
            return true;
        return jj_scan_token(84);
    }

    private static final boolean jj_3_30() {
        if (jj_scan_token(57))
            return true;
        if (jj_3R_119())
            return true;
        return jj_scan_token(85);
    }

    private static final boolean jj_3_29() {
        if (jj_3R_118())
            return true;
        return jj_scan_token(87);
    }

    private static final boolean jj_3R_381() {
        return jj_scan_token(100);
    }

    private static final boolean jj_3R_345() {
        Token xsp = jj_scanpos;
        if (jj_3R_381()) {
            jj_scanpos = xsp;
            if (jj_3R_382()) {
                jj_scanpos = xsp;
                return jj_3R_383();
            }
        }
        return false;
    }

    private static final boolean jj_3R_173() {
        Token xsp = jj_scanpos;
        if (jj_3_29())
            jj_scanpos = xsp;
        if (jj_scan_token(54))
            return true;
        if (jj_3R_119())
            return true;
        return jj_scan_token(85);
    }

    private static final boolean jj_3R_125() {
        Token xsp = jj_scanpos;
        if (jj_3R_179()) {
            jj_scanpos = xsp;
            if (jj_3R_180()) {
                jj_scanpos = xsp;
                return jj_3R_181();
            }
        }
        return false;
    }

    private static final boolean jj_3R_179() {
        if (jj_scan_token(79))
            return true;
        if (jj_3R_126())
            return true;
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_253()) {
                jj_scanpos = xsp;
                return jj_scan_token(80);
            }
        }
    }

    private static final boolean jj_3R_332() {
        if (jj_3R_118())
            return true;
        Token xsp = jj_scanpos;
        if (jj_3R_345())
            jj_scanpos = xsp;
        return false;
    }

    private static final boolean jj_3R_267() {
        return jj_3R_119();
    }

    private static final boolean jj_3R_331() {
        return jj_3R_344();
    }

    private static final boolean jj_3R_330() {
        return jj_3R_343();
    }

    private static final boolean jj_3R_172() {
        if (jj_scan_token(57))
            return true;
        if (jj_3R_119())
            return true;
        return jj_scan_token(85);
    }

    private static final boolean jj_3_39() {
        return jj_3R_125();
    }

    private static final boolean jj_3R_117() {
        Token xsp = jj_scanpos;
        if (jj_3R_172()) {
            jj_scanpos = xsp;
            return jj_3R_173();
        }
        return false;
    }

    private static final boolean jj_3R_297() {
        Token xsp = jj_scanpos;
        if (jj_3R_330()) {
            jj_scanpos = xsp;
            if (jj_3R_331()) {
                jj_scanpos = xsp;
                return jj_3R_332();
            }
        }
        return false;
    }

    private static final boolean jj_3R_268() {
        return jj_3R_219();
    }

    private static final boolean jj_3R_477() {
        return jj_3R_481();
    }

    private static final boolean jj_3R_159() {
        return jj_3R_144();
    }

    private static final boolean jj_3R_476() {
        return jj_3R_480();
    }

    private static final boolean jj_3R_479() {
        return jj_scan_token(90);
    }

    private static final boolean jj_3R_478() {
        return jj_scan_token(91);
    }

    private static final boolean jj_3R_106() {
        while (true) {
            Token xsp = jj_scanpos;
            if (jj_3R_159()) {
                jj_scanpos = xsp;
                if (jj_scan_token(76))
                    return true;
                xsp = jj_scanpos;
                if (jj_3R_267())
                    jj_scanpos = xsp;
                xsp = jj_scanpos;
                if (jj_3R_268())
                    jj_scanpos = xsp;
                return false;
            }
        }
    }

    private static final boolean jj_3R_475() {
        Token xsp = jj_scanpos;
        if (jj_3R_478()) {
            jj_scanpos = xsp;
            if (jj_3R_479())
                return true;
        }
        return jj_3R_458();
    }

    private static final boolean jj_3R_474() {
        Token xsp = jj_scanpos;
        if (jj_3R_475()) {
            jj_scanpos = xsp;
            if (jj_3R_476()) {
                jj_scanpos = xsp;
                return jj_3R_477();
            }
        }
        return false;
    }

    private static final boolean jj_3R_400() {
        return jj_scan_token(85);
    }

    private static final boolean jj_3_28() {
        return jj_3R_117();
    }

    private static final boolean jj_3R_353() {
        return jj_3R_273();
    }

    private static void jj_la1_0() {
        jj_la1_0 = new int[]{
                0, 541106176, 0, 541106176, 32768, 0, 0, 0, 40960, 677748736,
                40960, 40960, 33554432, 0, 32768, 0, 32768, 0, 677748736, 0,
                32768, 0, 0, 40960, 40960, 0, 1073741824, 0, 677748736, 40960,
                40960, 0, 0, 0, 0, 0, 0, 0, 0, 136675328,
                40960, 40960, 40960, 40960, 0, 1073741824, 677748736, 0, 0, 0,
                0, 0, 0, 136675328, 32768, 32768, 0, 0, 0, -2010841088,
                -2010841088, 0, 40960, 40960, 0, 0, 0, 40960, 40960, 0,
                0, 0, 136675328, 32768, 32768, 0, 0, 32768, 0, 32768,
                0, 0, 0, -1922580480, -2010841088, 0, 0, 136642560, 136642560, 0,
                136642560, 136642560, 0, 1073741824, 1073741824, 136642560, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, -2010841088, 0, 0, -2010841088,
                0, Integer.MIN_VALUE, 0, 0, 0, 0, Integer.MIN_VALUE, 0, 0, Integer.MIN_VALUE,
                Integer.MIN_VALUE, -2010841088, 0, 0, 0, 0, 0, 0, -1926807552, -1922580480,
                -1922613248, 32768, 32768, 0, 0, 0, 0, -2010841088, 34078720, -1922580480,
                34078720, 0, 268435456, -2010808320, -2010841088, -2010841088, -2010841088, 0, 0, 0,
                -2010841088, 1048576, 0, -1922580480, 0, -2010808320, 0, 0, -2010808320, -2010808320,
                0, 1073741824, 0};
    }

    private static void jj_la1_1() {
        jj_la1_1 = new int[]{
                128, 2556929, 128, 2556929, 0, 2097152, 0, 0, 2555904, 272043525,
                262144, 262144, 0, 0, 2555904, 64, 0, 0, -1858658811, 0,
                0, 0, 0, 262145, 262145, 0, 0, 64, -1858658811, 2555905,
                2555905, 0, 0, 0, 0, 0, 0, 0, 0, 272042501,
                262144, 262144, 2555905, 2555905, 0, 0, -1858658811, 0, 0, 0,
                0, 0, 0, 272042501, 270991361, 270991361, 0, 0, 0, -1571788284,
                -1571788284, 0, 19337217, 19337217, 0, 134217728, 0, 19337217, 19337217, 0,
                0, 0, 1051141, 0, 0, 1, 0, 0, 458752, 0,
                458752, 0, 134217728, -405247443, -1571788284, 2097152, 0, 1051140, 1051140, 0,
                1051140, -2146432508, 0, 4194304, 4194304, 1051140, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 256, 0, 0,
                0, 0, 0, 0, 0, 0, -1571788284, 0, 0, -1571788284,
                0, 574644224, 0, 0, 0, 0, 574644224, 0, 0, 536887296,
                536870912, -1571788284, 0, 0, 0, 8192, 0, 0, -405247444, -405247443,
                -405247444, 0, 0, 1, 0, 0, 0, -1571788284, 0, -405247443,
                0, 0, 0, -1571788283, -1571788284, -1571788284, -1571788284, 0, 0, 0,
                -1571788284, 0, 2, -405247443, 0, -1571788284, 0, 0, -1571788284, -1571788284,
                0, 0, 0};
    }

    private static void jj_la1_2() {
        jj_la1_2 = new int[]{
                0, 2097160, 0, 2097160, 0, 0, 8388608, 2097152, 8, 2101257,
                0, 0, 0, 2097152, 8, 0, 4096, 4194304, 33689609, 2097152,
                0, 32768, 131072, 8, 8, 33554432, 0, 0, 33689609, 8,
                8, 2097152, 2097152, 2097152, 2097152, 2097152, 2097152, 2097152, 2097152, 4097,
                8, 8, 8, 8, 33554432, 0, 33558537, 2097152, 2097152, 2097152,
                2097152, 2097152, 2097152, 4097, 1, 1, 4194304, 16777216, 524288, 201497872,
                201497872, 4194304, 8, 8, 33554432, 0, 2228224, 8, 8, 33554432,
                524288, 4194304, 4096, 0, 0, 0, 4, 0, 0, 0,
                0, 33554432, 0, 2268434, 40208, 0, 524288, 4096, 4096, 524288,
                0, 4096, 4194304, 0, 0, 268439552, 4194304, 16777216, 16777216, 268435456,
                0, 0, 0, 0, 0, 1073741824, 1073741824, 0, -2113929216, -2113929216,
                0, 0, 0, 0, 0, 0, 201366800, 201326592, 201326592, 40208,
                524288, 201366800, 32768, 0, 0, 32768, 36112, 4096, 8945664, 3344,
                0, 201366800, 33554432, 131072, 557056, 0, 524288, 524288, 2268434, 2268434,
                2268434, 0, 0, 0, 4194304, 16777216, 16777216, 40208, 0, 2268434,
                0, 536870912, 0, 40208, 201366800, 40208, 40208, 4194304, 4096, 4096,
                201366800, 0, 0, 2268434, 4194304, 201497872, 32768, 4194304, 201497872, 201497872,
                4194304, 0, 0};
    }

    private static void jj_la1_3() {
        jj_la1_3 = new int[]{
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 240,
                240, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 48, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 67076096, 67076096, 0,
                4, 8, 2048, 4096, 1024, 2, 2, 0, 268435457, 268435457,
                16384, 192, 192, 8960, 8960, 192, 240, 0, 0, 0,
                0, 0, 0, 48, 48, 0, 0, 0, 0, 0,
                0, 240, 0, 0, 0, 0, 0, 0, 48, 48,
                48, 0, 0, 0, 0, 67076144, 67076144, 48, 0, 48,
                0, 0, 0, 48, 240, 48, 48, 0, 0, 0,
                240, 0, 0, 48, 0, 240, 0, 0, 240, 240,
                0, 0, 1024};
    }

    public static void ReInit(InputStream stream) {
        ReInit(stream, null);
    }

    public static void ReInit(InputStream stream, String encoding) {
        try {
            jj_input_stream.ReInit(stream, encoding, 1, 1);
        } catch (UnsupportedEncodingException e) {
            throw new RuntimeException(e);
        }
        JavaCCParserTokenManager.ReInit(jj_input_stream);
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        int i;
        for (i = 0; i < 173; ) {
            jj_la1[i] = -1;
            i++;
        }
        for (i = 0; i < jj_2_rtns.length; ) {
            jj_2_rtns[i] = new JJCalls();
            i++;
        }
    }

    public static void ReInit(Reader stream) {
        jj_input_stream.ReInit(stream, 1, 1);
        JavaCCParserTokenManager.ReInit(jj_input_stream);
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        int i;
        for (i = 0; i < 173; ) {
            jj_la1[i] = -1;
            i++;
        }
        for (i = 0; i < jj_2_rtns.length; ) {
            jj_2_rtns[i] = new JJCalls();
            i++;
        }
    }

    private static final Token jj_consume_token(int kind) throws ParseException {
        Token oldToken;
        if ((oldToken = token).next != null) {
            token = token.next;
        } else {
            token = token.next = JavaCCParserTokenManager.getNextToken();
        }
        jj_ntk = -1;
        if (token.kind == kind) {
            jj_gen++;
            if (++jj_gc > 100) {
                jj_gc = 0;
                for (int i = 0; i < jj_2_rtns.length; i++) {
                    JJCalls c = jj_2_rtns[i];
                    while (c != null) {
                        if (c.gen < jj_gen)
                            c.first = null;
                        c = c.next;
                    }
                }
            }
            return token;
        }
        token = oldToken;
        jj_kind = kind;
        throw generateParseException();
    }

    private static final boolean jj_scan_token(int kind) {
        if (jj_scanpos == jj_lastpos) {
            jj_la--;
            if (jj_scanpos.next == null) {
                jj_lastpos = jj_scanpos = jj_scanpos.next = JavaCCParserTokenManager.getNextToken();
            } else {
                jj_lastpos = jj_scanpos = jj_scanpos.next;
            }
        } else {
            jj_scanpos = jj_scanpos.next;
        }
        if (jj_rescan) {
            int i = 0;
            Token tok = token;
            while (tok != null && tok != jj_scanpos) {
                i++;
                tok = tok.next;
            }
            if (tok != null)
                jj_add_error_token(kind, i);
        }
        if (jj_scanpos.kind != kind)
            return true;
        if (jj_la == 0 && jj_scanpos == jj_lastpos)
            throw jj_ls;
        return false;
    }

    public static final Token getNextToken() {
        if (token.next != null) {
            token = token.next;
        } else {
            token = token.next = JavaCCParserTokenManager.getNextToken();
        }
        jj_ntk = -1;
        jj_gen++;
        return token;
    }

    public static final Token getToken(int index) {
        Token t = lookingAhead ? jj_scanpos : token;
        for (int i = 0; i < index; i++) {
            if (t.next != null) {
                t = t.next;
            } else {
                t = t.next = JavaCCParserTokenManager.getNextToken();
            }
        }
        return t;
    }

    private static final int jj_ntk() {
        if ((jj_nt = token.next) == null)
            return jj_ntk = (token.next = JavaCCParserTokenManager.getNextToken()).kind;
        return jj_ntk = jj_nt.kind;
    }

    private static void jj_add_error_token(int kind, int pos) {
        if (pos >= 100)
            return;
        if (pos == jj_endpos + 1) {
            jj_lasttokens[jj_endpos++] = kind;
        } else if (jj_endpos != 0) {
            jj_expentry = new int[jj_endpos];
            for (int i = 0; i < jj_endpos; i++)
                jj_expentry[i] = jj_lasttokens[i];
            boolean exists = false;
            for (Enumeration<int[]> e = jj_expentries.elements(); e.hasMoreElements(); ) {
                int[] oldentry = e.nextElement();
                if (oldentry.length == jj_expentry.length) {
                    exists = true;
                    for (int j = 0; j < jj_expentry.length; j++) {
                        if (oldentry[j] != jj_expentry[j]) {
                            exists = false;
                            break;
                        }
                    }
                    if (exists)
                        break;
                }
            }
            if (!exists)
                jj_expentries.addElement(jj_expentry);
            if (pos != 0)
                jj_lasttokens[(jj_endpos = pos) - 1] = kind;
        }
    }

    public static ParseException generateParseException() {
        jj_expentries.removeAllElements();
        boolean[] la1tokens = new boolean[125];
        int i;
        for (i = 0; i < 125; i++)
            la1tokens[i] = false;
        if (jj_kind >= 0) {
            la1tokens[jj_kind] = true;
            jj_kind = -1;
        }
        for (i = 0; i < 173; i++) {
            if (jj_la1[i] == jj_gen)
                for (int k = 0; k < 32; k++) {
                    if ((jj_la1_0[i] & 1 << k) != 0)
                        la1tokens[k] = true;
                    if ((jj_la1_1[i] & 1 << k) != 0)
                        la1tokens[32 + k] = true;
                    if ((jj_la1_2[i] & 1 << k) != 0)
                        la1tokens[64 + k] = true;
                    if ((jj_la1_3[i] & 1 << k) != 0)
                        la1tokens[96 + k] = true;
                }
        }
        for (i = 0; i < 125; i++) {
            if (la1tokens[i]) {
                jj_expentry = new int[1];
                jj_expentry[0] = i;
                jj_expentries.addElement(jj_expentry);
            }
        }
        jj_endpos = 0;
        jj_rescan_token();
        jj_add_error_token(0, 0);
        int[][] exptokseq = new int[jj_expentries.size()][];
        for (int j = 0; j < jj_expentries.size(); j++)
            exptokseq[j] = jj_expentries.elementAt(j);
        return new ParseException(token, exptokseq, tokenImage);
    }

    public static final void enable_tracing() {
    }

    public static final void disable_tracing() {
    }

    private static final void jj_rescan_token() {
        jj_rescan = true;
        for (int i = 0; i < 62; i++) {
            try {
                JJCalls p = jj_2_rtns[i];
                do {
                    if (p.gen > jj_gen) {
                        jj_la = p.arg;
                        jj_lastpos = jj_scanpos = p.first;
                        switch (i) {
                            case 0:
                                jj_3_1();
                                break;
                            case 1:
                                jj_3_2();
                                break;
                            case 2:
                                jj_3_3();
                                break;
                            case 3:
                                jj_3_4();
                                break;
                            case 4:
                                jj_3_5();
                                break;
                            case 5:
                                jj_3_6();
                                break;
                            case 6:
                                jj_3_7();
                                break;
                            case 7:
                                jj_3_8();
                                break;
                            case 8:
                                jj_3_9();
                                break;
                            case 9:
                                jj_3_10();
                                break;
                            case 10:
                                jj_3_11();
                                break;
                            case 11:
                                jj_3_12();
                                break;
                            case 12:
                                jj_3_13();
                                break;
                            case 13:
                                jj_3_14();
                                break;
                            case 14:
                                jj_3_15();
                                break;
                            case 15:
                                jj_3_16();
                                break;
                            case 16:
                                jj_3_17();
                                break;
                            case 17:
                                jj_3_18();
                                break;
                            case 18:
                                jj_3_19();
                                break;
                            case 19:
                                jj_3_20();
                                break;
                            case 20:
                                jj_3_21();
                                break;
                            case 21:
                                jj_3_22();
                                break;
                            case 22:
                                jj_3_23();
                                break;
                            case 23:
                                jj_3_24();
                                break;
                            case 24:
                                jj_3_25();
                                break;
                            case 25:
                                jj_3_26();
                                break;
                            case 26:
                                jj_3_27();
                                break;
                            case 27:
                                jj_3_28();
                                break;
                            case 28:
                                jj_3_29();
                                break;
                            case 29:
                                jj_3_30();
                                break;
                            case 30:
                                jj_3_31();
                                break;
                            case 31:
                                jj_3_32();
                                break;
                            case 32:
                                jj_3_33();
                                break;
                            case 33:
                                jj_3_34();
                                break;
                            case 34:
                                jj_3_35();
                                break;
                            case 35:
                                jj_3_36();
                                break;
                            case 36:
                                jj_3_37();
                                break;
                            case 37:
                                jj_3_38();
                                break;
                            case 38:
                                jj_3_39();
                                break;
                            case 39:
                                jj_3_40();
                                break;
                            case 40:
                                jj_3_41();
                                break;
                            case 41:
                                jj_3_42();
                                break;
                            case 42:
                                jj_3_43();
                                break;
                            case 43:
                                jj_3_44();
                                break;
                            case 44:
                                jj_3_45();
                                break;
                            case 45:
                                jj_3_46();
                                break;
                            case 46:
                                jj_3_47();
                                break;
                            case 47:
                                jj_3_48();
                                break;
                            case 48:
                                jj_3_49();
                                break;
                            case 49:
                                jj_3_50();
                                break;
                            case 50:
                                jj_3_51();
                                break;
                            case 51:
                                jj_3_52();
                                break;
                            case 52:
                                jj_3_53();
                                break;
                            case 53:
                                jj_3_54();
                                break;
                            case 54:
                                jj_3_55();
                                break;
                            case 55:
                                jj_3_56();
                                break;
                            case 56:
                                jj_3_57();
                                break;
                            case 57:
                                jj_3_58();
                                break;
                            case 58:
                                jj_3_59();
                                break;
                            case 59:
                                jj_3_60();
                                break;
                            case 60:
                                jj_3_61();
                                break;
                            case 61:
                                jj_3_62();
                                break;
                        }
                    }
                    p = p.next;
                } while (p != null);
            } catch (LookaheadSuccess ls) {
            }
        }
        jj_rescan = false;
    }

    private static final void jj_save(int index, int xla) {
        JJCalls p = jj_2_rtns[index];
        while (p.gen > jj_gen) {
            if (p.next == null) {
                p = p.next = new JJCalls();
                break;
            }
            p = p.next;
        }
        p.gen = jj_gen + xla - jj_la;
        p.first = token;
        p.arg = xla;
    }

    public void ReInit(JavaCCParserTokenManager tm) {
        token_source = tm;
        token = new Token();
        jj_ntk = -1;
        jj_gen = 0;
        int i;
        for (i = 0; i < 173; ) {
            jj_la1[i] = -1;
            i++;
        }
        for (i = 0; i < jj_2_rtns.length; ) {
            jj_2_rtns[i] = new JJCalls();
            i++;
        }
    }

    static class PrimarySuffixReturnValue {
        static final int UNDEFINED = -1;

        static final int THIS = 0;

        static final int ALLOCATION_EXPR = 1;

        static final int INDEX_EXPR = 2;

        static final int IDENTIFIER = 3;

        static final int ARGUMENTS = 4;

        static final int SUPER = 5;

        int type = -1;

        Expression expr = null;

        Identifier id = null;

        ASTList<Expression> args = null;

        ASTList<TypeArgumentDeclaration> typeArgs = null;
    }

    static class PrimaryPrefixReturnValue {
        static final int UNDEFINED = -1;

        static final int LITERAL = 0;

        static final int THIS = 1;

        static final int SUPER_MEMBER = 2;

        static final int PARENTHESIZED_EXPR = 3;

        static final int ALLOCATION_EXPR = 4;

        static final int CLASS_REF = 5;

        static final int QUALIFIED_NAME = 6;

        int type = -1;

        Literal literal = null;

        Expression expr = null;

        TypeReference typeref = null;

        UncollatedReferenceQualifier name = null;
    }

    private static final class LookaheadSuccess extends Error {
        private LookaheadSuccess() {
        }
    }

    static final class JJCalls {
        int gen;

        Token first;

        int arg;

        JJCalls next;
    }
}
