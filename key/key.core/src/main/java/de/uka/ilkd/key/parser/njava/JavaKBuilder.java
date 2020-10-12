package de.uka.ilkd.key.parser.njava;

import de.uka.ilkd.key.java.recoderext.*;
import de.uka.ilkd.key.java.recoderext.adt.EmptyMapLiteral;
import de.uka.ilkd.key.java.recoderext.adt.EmptySeqLiteral;
import de.uka.ilkd.key.java.recoderext.adt.EmptySetLiteral;
import de.uka.ilkd.key.java.recoderext.adt.MethodSignature;
import de.uka.ilkd.key.nparser.JavaKBaseVisitor;
import de.uka.ilkd.key.nparser.JavaKLexer;
import de.uka.ilkd.key.nparser.JavaKParser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import recoder.abstraction.TypeArgument.WildcardMode;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.Assignment;
import recoder.java.expression.Literal;
import recoder.java.expression.Operator;
import recoder.java.expression.operator.PreDecrement;
import recoder.java.expression.operator.PreIncrement;
import recoder.java.expression.operator.TypeCast;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.parser.ParseException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (10/11/20)
 */
public class JavaKBuilder extends JavaKBaseVisitor<Object> {
    //region copied
    private static ProofJavaProgramFactory factory = (ProofJavaProgramFactory) ProofJavaProgramFactory.getInstance();

    static boolean superAllowed = true;
    private TypeDeclaration currentClass;

    private static boolean isSuperAllowed() {
        return superAllowed;
    }

    private static void setAllowSuper(boolean b) {
        superAllowed = b;
    }

    /**
     * temporary valid variable that is used to return an additional
     * argument from parser method VariableDeclaratorId, since such an
     * id may have a dimension
     */
    private static int tmpDimension;

    /**
     * all comments in a global list.
     */
    private static List<Comment> comments = new ArrayList<>();

    /**
     * reuseable position object.
     */
    private static SourceElement.Position position
            = new SourceElement.Position(0, 0);

    private static void copyPrefixInfo(SourceElement oldResult,
                                       SourceElement newResult) {
        newResult.setRelativePosition(oldResult.getRelativePosition());
        newResult.setStartPosition(oldResult.getStartPosition());
        newResult.setEndPosition(oldResult.getEndPosition());
    }

    public void finish(SourceElement element, ParserRuleContext ctx) {
        setPrefixInfo(element, ctx);
        setPostfixInfo(element, ctx);
        checkConstruction(element);
    }

    protected void setPrefixInfo(SourceElement constrResult, ParserRuleContext ctx) {
        position.setPosition(0, 0);
        constrResult.setRelativePosition(position);
        position.setPosition(ctx.start.getLine(), ctx.start.getCharPositionInLine());
        constrResult.setStartPosition(position);
    }

    protected void setPostfixInfo(SourceElement constrResult, ParserRuleContext ctx) {
        int len = ctx.stop.getStopIndex() - ctx.start.getStartIndex();
        position.setPosition(ctx.stop.getLine(), ctx.stop.getCharPositionInLine() + len);
        constrResult.setEndPosition(position);
    }

    public static List<Comment> getComments() {
        return comments;
    }


    /**
     * checks whether or not the tree construction result is valid.
     * Currently this only checks whether or not the result is <tt>null</tt>.
     *
     * @param constrResult the result of a factory call
     * @throws ParseException if the result is not legal
     */
    protected void checkConstruction(SourceElement constrResult) throws RuntimeException {
        if (constrResult == null) {
            //TODO replace a different one
            throw new RuntimeException("An illegal null object was created during tree construction");
        }
        // insert check code here!!
    }

    private static void checkConstruction(ASTList<? extends ProgramElement> constrResult) throws ParseException {
        if (constrResult == null) {
            throw new ParseException("An illegal null list was created during tree construction");
        }
        // insert check code here!!
    }

    /**
     * inner class that is only used to return results from
     * primary suffix syntax rule
     *
     * @author RN
     */
    static class PrimarySuffixReturnValue {
        // the following constants represent the various sub rules

        /**
         * indicates that the result is currently undefined
         */
        static final int UNDEFINED = -1;
        /**
         * production was <pre>"." "this"</pre>
         */
        static final int THIS = 0;
        /**
         * production was <pre>"." AllocationExpression</pre>
         */
        static final int ALLOCATION_EXPR = 1;
        /**
         * production was <pre> Expression </pre>
         */
        static final int INDEX_EXPR = 2;
        /**
         * production was <pre>"." <IDENTIFIER></pre>
         */
        static final int IDENTIFIER = 3;
        /**
         * production was <pre>Arguments</pre>
         */
        static final int ARGUMENTS = 4;
        /**
         * production was <pre>super</pre>
         */
        static final int SUPER = 5;

        /**
         * indicates the type of the result
         */
        int type = UNDEFINED;

        /**
         * valid iff <tt>type</tt> is <tt>ALLOCATION_EXPR</tt> or
         * <tt>INDEX_EXPR</tt>
         */
        Expression expr = null;

        /**
         * valid iff <tt>type</tt> is <tt>IDENTIFIER</tt>
         */
        Identifier id = null;


        /**
         * valid iff <tt>type</tt> is <tt>ARGUMENTS</tt>
         */
        ASTList<Expression> args = null;

        /**
         * valid iff <tt>type</tt> is <tt>IDENTIFIER</tt> and
         * it is an explicit generic method invocation
         */
        ASTList<TypeArgumentDeclaration> typeArgs = null;
    }


    /**
     * inner class that is only used to return results from
     * primary prefix syntax rule
     *
     * @author RN
     */
    static class PrimaryPrefixReturnValue {

        // the following constants represent the various sub rules

        /**
         * indicates that the result is currently undefined
         */
        static final int UNDEFINED = -1;
        /**
         * production was <pre>Literal</pre>
         */
        static final int LITERAL = 0;
        /**
         * production was <pre>"this"</pre>
         */
        static final int THIS = 1;
        /**
         * production was <pre>"super" "." <IDENTIFIER></pre>
         */
        static final int SUPER_MEMBER = 2;
        /**
         * production was <pre> Expression </pre>
         */
        static final int PARENTHESIZED_EXPR = 3;
        /**
         * production was <pre>AllocationExpression</pre>
         */
        static final int ALLOCATION_EXPR = 4;
        /**
         * production was <pre>ResultType "." "class"</pre>
         */
        static final int CLASS_REF = 5;
        /**
         * production was <pre>Name</pre>
         */
        static final int QUALIFIED_NAME = 6;
        /**
         * production was <pre>"@(" Expression </pre>
         */
        static final int PASSIVE_EXPR = 7;

        /**
         * production was something like <pre>"&93;seq_reverse(" Expression </pre>.
         * Extension to Java/JML with ADTs.
         *
         * @since 1.7.2118
         */
        static final int ADT_CONSTRUCT = 42;

        /**
         * indicates the type of the result
         */
        int type = UNDEFINED;

        /**
         * valid iff <tt>type</tt> is <tt>LITERAL</tt>
         */
        Literal literal = null;

        /**
         * valid iff <tt>type</tt> is <tt>PARENTHESED_EXPR</tt>
         * or <tt>ALLOCATION_EXPR</tt>
         */
        Expression expr = null;

        /**
         * valid iff <tt>type</tt> is <tt>CLASS_REF</tt>
         */
        TypeReference typeref = null;

        /**
         * valid iff <tt>type</tt> is <tt>QUALIFIED_NAME</tt> or
         * <tt>SUPER_MEMBER</tt>
         */
        UncollatedReferenceQualifier name = null;

    }

    /**
     * return value containers for primary expression.
     * need only be allocated once per parser.
     */
    static PrimarySuffixReturnValue suffix = new PrimarySuffixReturnValue();
    static PrimaryPrefixReturnValue prefix = new PrimaryPrefixReturnValue();
    //endregion

    //region helper

    /**
     * Helper function for avoiding cast.
     *
     * @param ctx
     * @param <T>
     * @return
     */
    protected <T> @Nullable T accept(@Nullable RuleContext ctx) {
        if (ctx == null) {
            return null;
        }
        return (T) ctx.accept(this);
    }

    protected <T> @NotNull T expect(@NotNull RuleContext ctx) {
        return (T) ctx.accept(this);
    }

    protected <T> T acceptFirst(Collection<? extends RuleContext> seq) {
        if (seq.isEmpty()) return null;
        return accept(seq.iterator().next());
    }

    protected <T> T acceptFirst(ParserRuleContext... ctxs) {
        for (ParserRuleContext ctx : ctxs) {
            if (ctx != null) {
                return (T) ctx.accept(this);
            }
        }
        return null;
    }

    protected <T> @NotNull T oneOf(ParserRuleContext... ctxs) {
        for (ParserRuleContext ctx : ctxs) {
            if (ctx != null) {
                return (T) ctx.accept(this);
            }
        }
        throw new IllegalArgumentException("no non-null context given");
    }

    protected <T extends SourceElement> ASTList<T> mapOf(Collection<? extends ParserRuleContext> argument) {
        ASTList<T> l = new ASTArrayList<>();
        argument.stream().map(it -> (T) it.accept(this)).forEach(it -> l.add(it));
        return l;
    }

    protected void each(RuleContext... ctx) {
        for (RuleContext c : ctx) accept(c);
    }

    protected void each(Collection<? extends ParserRuleContext> argument) {
        for (RuleContext c : argument) accept(c);
    }
    //endregion

    protected <T2> List<T2> mapMapOf(List<? extends RuleContext>... ctxss) {
        return Arrays.stream(ctxss)
                .flatMap(it -> it.stream().map(a -> (T2) accept(a)))
                .collect(Collectors.toList());
    }

    //endregion

    @Override
    public CompilationUnit visitCompilationUnit(JavaKParser.CompilationUnitContext ctx) {
        PackageSpecification ps = accept(ctx.packageDeclaration());
        ASTList<Import> imports = mapOf(ctx.importDeclaration());
        ASTList<TypeDeclaration> declarations = mapOf(ctx.typeDeclaration());
        CompilationUnit result = factory.createCompilationUnit(ps, imports, declarations);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitPackageDeclaration(JavaKParser.PackageDeclarationContext ctx) {
        ASTList<AnnotationUseSpecification> annotations = new ASTArrayList<AnnotationUseSpecification>();
        AnnotationUseSpecification annot = null;//TODO? AnnotationUse();
        annotations.add(annot);
        annotations.trimToSize();
        PackageSpecification result = factory.createPackageSpecification();
        result.setAnnotations(annotations);
        UncollatedReferenceQualifier qn = accept(ctx.packageName());
        result.setPackageReference(qn.toPackageReference());
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitImportDeclaration(JavaKParser.ImportDeclarationContext ctx) {
        Import result = factory.createImport();
        UncollatedReferenceQualifier qn = expect(ctx.qualifiedName());
        result.setMultiImport(ctx.MUL() != null);
        result.setStaticImport(ctx.STATIC() != null);
        if (result.isStaticImport()) {
            if (result.isMultiImport()) {
                result.setStaticIdentifier(qn.getIdentifier());
            } else {
                result.setStaticIdentifier(qn.toTypeReference().getIdentifier());
            }
        } else {
            if (result.isMultiImport()) {
                result.setReference(qn);
            } else {
                result.setReference(qn.toTypeReference());
            }
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitStaticImportOnDemandDeclaration(JavaKParser.StaticImportOnDemandDeclarationContext ctx) {
        UncollatedReferenceQualifier qn = expect(ctx.typeName());
        Import result = factory.createImport();
        result.setMultiImport(true);
        result.setStaticImport(true);
        result.setReference(qn.toTypeReference());
        finish(result, ctx);
        return result;
    }


    public Object getModifier(String s) {
        switch (s) {
            case "protected":
                return factory.createProtected();
            case "private":
                return factory.createPrivate();
            case "static":
                return factory.createStatic();
            case "final":
                return factory.createFinal();
            case "transient":
                return factory.createTransient();
            case "volatile":
                return factory.createVolatile();
            case "strictfp":
                return factory.createStrictFp();
            case "public":
                return factory.createPublic();
            case "abstract":
                return factory.createAbstract();
            default:
                //TODO return new AnnotationUse();
                return null;
        }

    }

    @Override
    public Object visitInterfaceModifier(JavaKParser.InterfaceModifierContext ctx) {
        switch (ctx.getText()) {
            case "strictfp":
                return factory.createStrictFp();
            case "public":
                return factory.createPublic();
            case "protected":
                return factory.createProtected();
            case "private":
                return factory.createPrivate();
            case "static":
                return factory.createStatic();
            case "abstract":
                return factory.createAbstract();
            default:
                //TODO return new AnnotationUse();
                return null;
        }
    }

    @Override
    public AnnotationDeclaration visitAnnotationTypeDeclaration(JavaKParser.AnnotationTypeDeclarationContext ctx) {
        ASTList<MemberDeclaration> members = new ASTArrayList<MemberDeclaration>();
        MethodDeclaration md;
        FieldDeclaration fd;
        TypeDeclaration td;
        ASTList<DeclarationSpecifier> declSpecs = new ASTArrayList<DeclarationSpecifier>(), methodDs;
        AnnotationDeclaration result = new AnnotationDeclaration();
        ASTList<DeclarationSpecifier> modifiers = mapOf(ctx.interfaceModifier());
        Identifier name = accept(ctx.identifier());
        methodDs = new ASTArrayList<>();
        TypeReference methodRes = null;//TODO ? Type();
        Expression methodDefExpr = null;
        Identifier methodName = null;
        md = factory.createAnnotationPropertyDeclaration(methodDs, methodRes, methodName, methodDefExpr);
        members.add(md);
        result.setDeclarationSpecifiers(declSpecs);
        result.setIdentifier(name);
        result.setMembers(members);
        finish(result, ctx);
        return result;
    }

    private EnumDeclaration currentEnum;

    @Override
    public EnumDeclaration visitEnumDeclaration(JavaKParser.EnumDeclarationContext ctx) {
        ASTList<DeclarationSpecifier> modifiers = mapOf(ctx.classModifier());
        EnumDeclaration result = currentEnum = new EnumDeclaration();
        if (modifiers.size() != 0)
            result.setDeclarationSpecifiers(modifiers);
        Identifier id = accept(ctx.identifier());
        result.setIdentifier(id);

        if (ctx.superinterfaces() != null) {
            Implements im = factory.createImplements();
            ASTList<UncollatedReferenceQualifier> nl = null;//TODO TypedNameList();
            ASTList<TypeReference> trl = new ASTArrayList<TypeReference>();
            for (int i = 0, s = nl.size(); i < s; i++) {
                TypeReference tr =
                        nl.get(i).toTypeReference();
                trl.add(tr);
            }
            im.setSupertypes(trl);
            result.setImplementedTypes(im);
            finish(im, ctx);
        }

        ASTList<MemberDeclaration> members = accept(ctx.enumBody());
        result.setMembers(members);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitEnumConstant(JavaKParser.EnumConstantContext ctx) {
        ASTList<DeclarationSpecifier> annotations = mapOf(ctx.enumConstantModifier());
        Identifier id = accept(ctx.identifier());
        ASTList<Expression> args = accept(ctx.argumentList());

        ClassDeclaration cd = null;
        if (ctx.classBody() != null) {
            cd = factory.createClassDeclaration();
            ASTList<MemberDeclaration> members = accept(ctx.classBody());
            cd.setMembers(members);
            finish(cd, ctx.classBody());
        }

        EnumClassDeclaration result = new EnumClassDeclaration();
        EnumConstructorReference ref = new EnumConstructorReference(args, cd);
        EnumConstantSpecification spec = new EnumConstantSpecification(id, ref);
        //TODO result.setEnumConstantSpecification(spec);
        result.setDeclarationSpecifiers(annotations);
        return result;
    }

    @Override
    public Object visitEnumConstantModifier(JavaKParser.EnumConstantModifierContext ctx) {
        return super.visitEnumConstantModifier(ctx);
    }

    @Override
    public Object visitEnumBodyDeclarations(JavaKParser.EnumBodyDeclarationsContext ctx) {
        currentClass = currentEnum;
        return super.visitEnumBodyDeclarations(ctx);
    }

	/*
@Override ClassDeclaration visitUnmodifiedClassDeclaration(JavaKParser.UnmodifiedClassDeclarationContext ctx)
    {
        ClassDeclaration                 result;
        UncollatedReferenceQualifier     qn;
        ASTList<UncollatedReferenceQualifier> nl;
        ASTList<MemberDeclaration>     mdl;
        Extends ex;
        Implements im;
        ASTList<TypeParameterDeclaration> typeParams = null;
        Identifier id;
    
        "class"  {
        result = factory.createClassDeclaration();
        setPrefixInfo(result);
    }

        id = ShortName()
        {
            result.setIdentifier(id);
        }

  [ typeParams = TypeParameters()
        {
            result.setTypeParameters(typeParams);
        }
  ]

  [ "extends"
        {
            ex = factory.createExtends();
            setPrefixInfo(ex);
        }
        qn = TypedName()
        {
            ex.setSupertypes(new ASTArrayList<TypeReference>(1));
            ex.getSupertypes().add(qn.toTypeReference());
            result.setExtendedTypes(ex);
        }
  ]
  [ "implements"
        {
            im = factory.createImplements();
            setPrefixInfo(im);
        }
        nl = TypedNameList()
        {
            ASTList<TypeReference> trl = new ASTArrayList<TypeReference>();
            for (int i = 0, s = nl.size(); i < s; i++) {
                TypeReference tr =
                        nl.get(i).toTypeReference();
                trl.add(tr);
            }
            im.setSupertypes(trl);
            result.setImplementedTypes(im);
        }
  ]
        mdl = ClassBody()
        {
            result.setMembers(mdl);
            checkConstruction(result);
            setPostfixInfo(result);
            return result;
        }
    }

@Override ASTList<MemberDeclaration> visitClassBody(JavaKParser.ClassBodyContext ctx)
    {
        ASTList<MemberDeclaration> result = new ASTArrayList<MemberDeclaration>();
        MemberDeclaration md;
    
        "{"
        (
                md = ClassBodyDeclaration()
        {
            result.add(md);
        }
  )*
        "}"
        {
            checkConstruction(result);
            return result;
        }
    }
	 */

	/*
@Override ClassDeclaration visitNestedClassDeclaration(JavaKParser.NestedClassDeclarationContext ctx)
    {
        ClassDeclaration result;
        ASTList<DeclarationSpecifier> ml = new ASTArrayList<DeclarationSpecifier>();
        DeclarationSpecifier m;
    
        (
                (
                        ( "static"    { m = factory.createStatic(); }    )
    | ( "abstract"  { m = factory.createAbstract(); }  )
    | ( "final"     { m = factory.createFinal(); }     )
    | ( "public"    { m = factory.createPublic(); }    )
    | ( "protected" { m = factory.createProtected(); } )
    | ( "private"   { m = factory.createPrivate(); }   )
    | ( "strictfp"  { m = factory.createStrictFp(); }  )
    | ( m = AnnotationUse() 						   )
    )
        {
            setPrefixInfo(m);
            setPostfixInfo(m);
            ml.add(m);
        }
  )*
        result = UnmodifiedClassDeclaration()
        {
            result.setDeclarationSpecifiers(ml);
            checkConstruction(result);
            setPostfixInfo(result);
            return result;
        }
    }
	 */

    @Override
    public Object visitNormalInterfaceDeclaration(JavaKParser.NormalInterfaceDeclarationContext ctx) {
        ASTList<DeclarationSpecifier> ml = mapOf(ctx.interfaceModifier());
        InterfaceDeclaration result = new InterfaceDeclaration();
        Identifier id = accept(ctx.identifier());
        result.setIdentifier(id);
        result.setDeclarationSpecifiers(ml);

        //TODO body
        ctx.interfaceBody();
        ctx.typeParameters();

        finish(result, ctx);
        return result;
    }

	/*
@Override InterfaceDeclaration visitUnmodifiedInterfaceDeclaration(JavaKParser.UnmodifiedInterfaceDeclarationContext ctx)
    {
        InterfaceDeclaration             result;
        ASTList<UncollatedReferenceQualifier> nl;
        ASTList<MemberDeclaration>     mdl = new ASTArrayList<MemberDeclaration>();
        MemberDeclaration                md;
        Extends ex;
        ASTList<TypeParameterDeclaration> typeParams = null;
        Identifier id;
    
        "interface"
        {
            result = factory.createInterfaceDeclaration();
            setPrefixInfo(result);
        }

        id = ShortName()
        {
            result.setIdentifier(id);
        }

  [ typeParams = TypeParameters()
        {
            result.setTypeParameters(typeParams);
        }
  ]
  [ "extends"
        {
            ex = factory.createExtends();
            setPrefixInfo(ex);
        }
        nl = TypedNameList()
        {
            ASTList<TypeReference> trl = new ASTArrayList<TypeReference>();
            for (int i = 0, s = nl.size(); i < s; i++) {
                TypeReference tr =
                        nl.get(i).toTypeReference();
                trl.add(tr);
            }
            ex.setSupertypes(trl);
            result.setExtendedTypes(ex);
        }
  ]
        "{"
        (
                md = InterfaceMemberDeclaration()
        {
            mdl.add(md);
        }
  )*
        "}"
        {
            result.setMembers(mdl);
            checkConstruction(result);
            setPostfixInfo(result);
            return result;
        }
    }

@Override MemberDeclaration visitInterfaceMemberDeclaration(JavaKParser.InterfaceMemberDeclarationContext ctx)
    {
        MemberDeclaration result;
    
        (
                LOOKAHEAD( ( "static" | "abstract" | "final" | "public" | "protected" | "private" | "strictfp" | AnnotationUse() )* "class" )
        (result = NestedClassDeclaration() (";")*) // patch
| LOOKAHEAD( ( "static" | "abstract" | "final" | "public" | "protected" | "private" | "strictfp" | AnnotationUse() )* "interface" )
        (result = NestedInterfaceDeclaration() (";")*) // patch
| LOOKAHEAD( MethodDeclarationLookahead() )
        (result = MethodDeclaration() (";")*) // patch
| LOOKAHEAD( EnumDeclaration() )
        (result = EnumDeclaration() (";")*)
| LOOKAHEAD( AnnotationTypeDeclaration() )
        (result = AnnotationTypeDeclaration() (";")*)
| (result = FieldDeclaration() (";")*) // patch
)
        {
            checkConstruction(result);
            setPostfixInfo(result);
            return result;
        }
    }
	 */

    @Override
    public Object visitFieldModifier(JavaKParser.FieldModifierContext ctx) {
        if (ctx.annotation() != null) throw new IllegalArgumentException();
        return getModifier(ctx.getText());
    }

    @Override
    public FieldDeclaration visitFieldDeclaration(JavaKParser.FieldDeclarationContext ctx) {
        ASTList<DeclarationSpecifier> ml = mapOf(ctx.fieldModifier());
        UncollatedReferenceQualifier qn;
        ASTArrayList<FieldSpecification> vl = new ASTArrayList<>();

        FieldDeclaration result = factory.createFieldDeclaration();

        TypeReference tr = expect(ctx.unannType());
        result.setDeclarationSpecifiers(ml);
        result.setTypeReference(tr);
        //TODO set member
        List<VariableSpecification> decls = accept(ctx.variableDeclaratorList());
        assert decls != null;
        for (VariableSpecification v : decls) {
            vl.add((FieldSpecification) v);
        }
        result.setFieldSpecifications(vl);
        finish(result, ctx);
        return result;
    }

    boolean isForField = true;

    @Override
    public VariableSpecification visitVariableDeclarator(JavaKParser.VariableDeclaratorContext ctx) {
        isForField = true;
        int dim;
        VariableSpecification result;
        Identifier id = accept(ctx.variableDeclaratorId());
        dim = tmpDimension;
        Expression init = accept(ctx.variableInitializer());
        if (isForField) {
            result = factory.createFieldSpecification(id, dim, init);
        } else {
            result = factory.createVariableSpecification(id, dim, init);
        }
        setPrefixInfo(result, ctx); // only after "=" !!!!!!!!!!!!!!!        // TODO: WP:
        checkConstruction(result);
        setPostfixInfo(result, ctx);
        return result;
    }

    @Override
    public Identifier visitVariableDeclaratorId(JavaKParser.VariableDeclaratorIdContext ctx) {
        Identifier result = accept(ctx.identifier());
        tmpDimension = ctx.dims().RBRACK().size();
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitArrayInitializer(JavaKParser.ArrayInitializerContext ctx) {
        ASTList<Expression> el = new ASTArrayList<>();
        ArrayInitializer result = factory.createArrayInitializer();
        List<Expression> init = accept(ctx.variableInitializerList());
        init.forEach(it -> el.add(it));
        result.setArguments(el);
        finish(result, ctx);
        return result;
    }

    @Override
    public MethodDeclaration visitMethodDeclaration(JavaKParser.MethodDeclarationContext ctx) {
        MethodDeclaration result = new MethodDeclaration();
        ASTList<DeclarationSpecifier> m = mapOf(ctx.methodModifier());
        Throws th = null;
        StatementBlock body = null;
        ASTList<TypeParameterDeclaration> typeParams = null;
        SourceElement dummy = null;

        if (ctx.methodHeader().typeParameters() != null) {
            typeParams = accept(ctx.methodHeader().typeParameters());
        }

        TypeReference tr = accept(ctx.methodHeader().result().unannType());


        ASTList<UncollatedReferenceQualifier> nl = null;
        if (ctx.methodHeader().throws_() != null) {
            th = factory.createThrows();
            setPrefixInfo(th, ctx);
            nl = accept(ctx.methodHeader().throws_().exceptionTypeList());
        }

        body = accept(ctx.methodBody());
        if (nl != null) {
            ASTList<TypeReference> trl = new ASTArrayList<TypeReference>();
            for (int i = 0, s = nl.size(); i < s; i++) {
                trl.add(nl.get(i).toTypeReference());
            }
            th.setExceptions(trl);
            result.setThrown(th);
        }
        result.setTypeParameters(typeParams);
        result.setDeclarationSpecifiers(m);
        result.setBody(body);
        finish(result, ctx);
        return result;
    }

    /*
    MethodDeclaration MethodDeclarator(TypeReference tr) :

    {
        Identifier id;
        ASTList<ParameterDeclaration> pdl;
        MethodDeclaration result;
    
        id = ShortName()
        pdl = FormalParameters()

        (  // array dims are indeed allowed after parameter list (!)
        {
            if (tr != null) {
                tr.setDimensions(tr.getDimensions() + 1);
            }
        }
  )*

        {
            result = factory.createMethodDeclaration();
            result.setIdentifier(id);
            result.setTypeReference(tr);
            result.setParameters(pdl);
            finish(result, ctx)
            return result;
        }
    }
     */

    @Override
    public ParameterDeclaration visitFormalParameter(JavaKParser.FormalParameterContext ctx) {
        ParameterDeclaration result;
        TypeReference tr;
        DeclarationSpecifier mod = null;
        Identifier id;
        VariableSpecification vspec;
        int dim;
        ASTList<DeclarationSpecifier> ml = null;
        boolean isVarArg = false;

        boolean final_ = true;
        if (/*isfinal*/ final_) {
            mod = factory.createFinal();
            setPrefixInfo(mod, ctx);
            setPostfixInfo(mod, ctx);
            if (ml == null) {
                ml = new ASTArrayList<DeclarationSpecifier>();
            }
            ml.add(mod);
        }

        tr = accept(ctx.unannType());
        //TODO isVarArg = true;

        id = accept(ctx.variableDeclaratorId());

        dim = tmpDimension; /*if (varArgSpec != null) dim++;*/

        result = factory.createParameterDeclaration(tr, id);
        if (ml != null) {
            result.setDeclarationSpecifiers(ml);
        }
        vspec = result.getVariables().get(0);
        vspec.setDimensions(dim);
        finish(result, ctx);
        result.setVarArg(isVarArg);
        return result;
    }

    /*TODO
    @Override
    public ConstructorDeclaration visitConstructorDeclaration(JavaKParser.ConstructorDeclarationContext ctx) {
        ConstructorDeclaration result;
        DeclarationSpecifier m = null;
        ASTList<DeclarationSpecifier> ml = new ASTArrayList<DeclarationSpecifier>();
        Identifier id;
        ASTList<ParameterDeclaration> pdl;
        ASTList<UncollatedReferenceQualifier> nl = null;
        SpecialConstructorReference scr = null;
        StatementBlock body;
        ASTList<Statement> stats = new ASTArrayList<Statement>();
        Statement stat;
        Throws th = null;

        {
            result = factory.createConstructorDeclaration();
            setPrefixInfo(result, ctx);
        }
        (m = AnnotationUse() {
            setPrefixInfo(m, ctx);
            setPostfixInfo(m, ctx);
            ml.add(m);
        })*
  [
        (
                ("public" {
            m = factory.createPublic();
        }    )
    |("protected" {
            m = factory.createProtected();
        } )
    |("private" {
            m = factory.createPrivate();
        }   )
   )
        {
            setPrefixInfo(m, ctx);
            setPostfixInfo(m, ctx);
            ml.add(m);
        }
        (m = AnnotationUse() {
            setPrefixInfo(m, ctx);
            setPostfixInfo(m, ctx);
            ml.add(m);
        })*
  ]
  [TypeParameters() ]
  <IDENTIFIER > {
                id = factory.createIdentifier(token.image);
        setPrefixInfo(id, ctx);
        setPostfixInfo(id, ctx);
  }
        pdl = FormalParameters()

                ["throws" {
            th = factory.createThrows();
            setPrefixInfo(th, ctx);
        }
        nl = TypedNameList() ]

        ("{"
        {
            body = factory.createStatementBlock();
            setPrefixInfo(body, ctx);
            body.setBody(stats);

            setAllowSuper(false);
        }
    [LOOKAHEAD(ExplicitConstructorInvocation())
        scr = ExplicitConstructorInvocation()
        {
            stats.add(scr);
        }
    ]
        {
            setAllowSuper(true);
        }
        (stat = BlockStatement()
        {
            stats.add(stat);
        }
    )*
        "}"
                |
                ";" {
            body = null;
        }
  )
        {
            if (body != null)
                setPostfixInfo(body, ctx);

            result.setIdentifier(id);
            result.setParameters(pdl);
            if (!ml.isEmpty())
                result.setDeclarationSpecifiers(ml);
            if (nl != null) {
                int s = nl.size();
                ASTList<TypeReference> trl = new ASTArrayList<TypeReference>(s);
                for (int i = 0; i < s; i++) {
                    trl.add(nl.get(i).toTypeReference());
                }
                result.setThrown(th);
            }
            result.setBody(body);
            checkConstruction(result);
            setPostfixInfo(result, ctx);
            return result;
        }
    }
*/
        /*TODO
    @Override
    public SpecialConstructorReference visitExplicitConstructorInvocation(JavaKParser.ExplicitConstructorInvocationContext ctx) {
        SpecialConstructorReference result;
        ASTList<Expression> args;
        Expression expr = null;

        (
                LOOKAHEAD("this"Arguments()";")
        "this"
        {
            result = factory.createThisConstructorReference();
            setPrefixInfo(result, ctx);
        }
        args = Arguments() ";"
        {
            result.setArguments(args);
        }
|
  [LOOKAHEAD(2) expr = PrimarExpression() "." ]
        "super"
        {
            result = factory.createSuperConstructorReference();
            setPrefixInfo(result, ctx);
        }
        args = Arguments() ";"
        {
            result.setArguments(args);
            ((SuperConstructorReference) result).setReferencePrefix((ReferencePrefix) expr);
        }
)
        {
            checkConstruction(result);
            setPostfixInfo(result, ctx);
            return result;
        }
    }
    */

        /*TODO

    @Override
    public ClassInitializer visitInitializer(JavaKParser.InitializerContext ctx) {
        ClassInitializer result;
        ASTList<DeclarationSpecifier> ml = null;
        StatementBlock block;
    
  ["static"
        {
            ml = new ASTArrayList<DeclarationSpecifier>();
            Static s = factory.createStatic();
            setPrefixInfo(s, ctx);
            setPostfixInfo(s, ctx);
            ml.add(s);
        }
  ]
        block = Block()
        {
            result = factory.createClassInitializer(block);
            setPrefixInfo(result, ctx);
            if (ml != null) {
                result.setDeclarationSpecifiers(ml);
            }
            checkConstruction(result);
            setPostfixInfo(result, ctx);
            return result;
        }
    }
    */

    /*
     * Type, name and expression syntax follows.
     */

    /*TODO
@Override
public TypeReference visitType(JavaKParser.TypeContext ctx) {
    TypeReference result;
    UncollatedReferenceQualifier qn;
    int dimension = 0;

    (
            result = PrimitiveType()
                    |
                    qn = TypedName()
    {
        result = qn.toTypeReference();
    }
  )
    (  {
        if (dimension == 0) setPrefixInfo(result, ctx);
        dimension++;
    } )*
    {
        result.setDimensions(dimension);
        setPostfixInfo(result, ctx);

        return result;
    }
}
     */

    @Override
    public TypeReference visitPrimitiveType(JavaKParser.PrimitiveTypeContext ctx) {
        Identifier id = factory.createIdentifier(ctx.getText());
        TypeReference result = factory.createTypeReference(id);
        finish(result, ctx);
        return result;
    }

    /*
    @Override
    public TypeReference visitResultType(JavaKParser.ResultTypeContext ctx) {
        int dimension = 0;
        TypeReference result;
        UncollatedReferenceQualifier qn;

        (
                "void"
        {
            Identifier id = factory.createIdentifier(token.image);
            setPrefixInfo(id, ctx);
            setPostfixInfo(id, ctx);
            result = factory.createTypeReference(id);
            setPrefixInfo(result, ctx);
        }
|
        (
                result = PrimitiveType()
                        |
                        qn = DeclarationTypedName() {
            result = qn.toTypeReference();
        }
)
        ({
        if (dimension == 0) setPrefixInfo(result, ctx);
        dimension++;
    } )*
)
        {
            result.setDimensions(dimension);
            checkConstruction(result);
            setPostfixInfo(result, ctx);
            return result;
        }
    }
    */

    /*public UncollatedReferenceQualifier visitName(JavaKParser.NameContext ctx) {
        UncollatedReferenceQualifier result;
        Identifier id;

        id = ShortName()
        {
            result = factory.createUncollatedReferenceQualifier(id);
        }

        (
                LOOKAHEAD(2) "." {
            setPrefixInfo(result, ctx);
        }
        id = ShortName()
        {
            result = factory.createUncollatedReferenceQualifier(result, id);
        }
  )*
        {
            checkConstruction(result);
            setPostfixInfo(result, ctx);
            return result;
        }
    }*/

    /*
     * Identical copy of TypedName, but lookahead is different for
     * TypeArgument, if ImplicitIdentifier follows!
     */

    /*
    @Override
    public UncollatedReferenceQualifier visitDeclarationTypedName(JavaKParser.DeclarationTypedNameContext ctx) {
        UncollatedReferenceQualifier result;
        Identifier id;
        ASTList<TypeArgumentDeclaration> typeArguments = null;

        id = ShortName()

                [LOOKAHEAD(TypeArguments() ("." | ShortName()))typeArguments = TypeArguments()]
        {
            result = factory.createUncollatedReferenceQualifier(id);
            result.setTypeArguments(typeArguments);
        }
        (
                LOOKAHEAD(2) "." {
            setPrefixInfo(result, ctx);
            setPostfixInfo(result, ctx);
        }
        id = ShortName()
        {
            typeArguments = null; // reset!
        }
    [LOOKAHEAD(TypeArguments() ("." | ShortName()))typeArguments = TypeArguments()]
        {
            result = factory.createUncollatedReferenceQualifier(result, id);
            result.setTypeArguments(typeArguments);
        }
  )*
        {
            setPostfixInfo(result, ctx);
            return result;
        }
    }
    */

    /*
    @Override
    public UncollatedReferenceQualifier visitTypedName(JavaKParser.TypedNameContext ctx) {
        UncollatedReferenceQualifier result;
        Identifier id;
        ASTList<TypeArgumentDeclaration> typeArguments = null;

        id = ShortName()

                [LOOKAHEAD(2) typeArguments = TypeArguments()]
        {
            result = factory.createUncollatedReferenceQualifier(id);
            result.setTypeArguments(typeArguments);
        }
        (
                LOOKAHEAD(2) "." {
            setPrefixInfo(result, ctx);
            setPostfixInfo(result, ctx);
        }
        id = ShortName()
        {
            typeArguments = null; // reset!
        }
    [LOOKAHEAD(2) typeArguments = TypeArguments()]
        {
            result = factory.createUncollatedReferenceQualifier(result, id);
            result.setTypeArguments(typeArguments);
        }
  )*
        {
            setPostfixInfo(result, ctx);
            return result;
        }
    }
    */

    @Override
    public ASTList<TypeArgumentDeclaration> visitTypeArguments(JavaKParser.TypeArgumentsContext ctx) {
        return expect(ctx.typeArgumentList());
    }

    @Override
    public Object visitTypeArgumentList(JavaKParser.TypeArgumentListContext ctx) {
        return mapOf(ctx.typeArgument());
    }

    @Override
    public TypeArgumentDeclaration visitTypeArgument(JavaKParser.TypeArgumentContext ctx) {
        if (ctx.referenceType() != null) {
            WildcardMode wm = WildcardMode.None;
            TypeReference t;
            TypeArgumentDeclaration result = new TypeArgumentDeclaration();
            t = accept(ctx.referenceType());
            finish(result, ctx);
            return result;
        } else {//wildcard mode
            return expect(ctx.wildcard());
        }
    }

    @Override
    public Object visitWildcard(JavaKParser.WildcardContext ctx) {
        TypeArgumentDeclaration result = new TypeArgumentDeclaration();
        ASTList<DeclarationSpecifier> annot = mapOf(ctx.annotation());
        WildcardMode wm = WildcardMode.Any;
        if (ctx.wildcardBounds() != null) {
            if (ctx.wildcardBounds().EXTENDS() != null)
                wm = WildcardMode.Extends;
            else
                wm = WildcardMode.Super;
            TypeReference t = expect(ctx.wildcardBounds().referenceType());
            result.setTypeReference(t);
        }
        finish(result, ctx);
        result.setWildcardMode(wm);
        return result;
    }

    /*
ASTList<UncollatedReferenceQualifier> NameList() :
{
  ASTList<UncollatedReferenceQualifier> result =
      new ASTArrayList<UncollatedReferenceQualifier>();
  UncollatedReferenceQualifier qn;

  qn = Name()
  {
    result.add(qn);
  }
  ( "," qn = Name()
    {
      result.add(qn);
    }
  )*
  {
    checkConstruction(result);
//    setPostfixInfo(result);
    return result;
  }
}
*/

    /*
    @Override
    public ASTList<UncollatedReferenceQualifier> visitTypedNameList(JavaKParser.TypedNameListContext ctx) {
        ASTList<UncollatedReferenceQualifier> result =
                new ASTArrayList<UncollatedReferenceQualifier>();
        UncollatedReferenceQualifier qn;

        qn = TypedName()
        {
            result.add(qn);
        }
        ("," qn = TypedName()
        {
            result.add(qn);
        }
  )*
        {
            return result;
        }
    }
    */

    /*
     * Expression syntax follows.
     */

    @Override
    public Assignment visitAssignmentOperator(JavaKParser.AssignmentOperatorContext ctx) {
        Assignment result;
        switch (ctx.getText()) {
            case "=":
                result = factory.createCopyAssignment();
                break;
            case "*=":
                result = factory.createTimesAssignment();
                break;
            case "/=":
                result = factory.createDivideAssignment();
                break;
            case "%=":
                result = factory.createModuloAssignment();
                break;
            case "+=":
                result = factory.createPlusAssignment();
                break;
            case "-=":
                result = factory.createMinusAssignment();
                break;
            case "<<=":
                result = factory.createShiftLeftAssignment();
                break;
            case ">>=":
                result = factory.createShiftRightAssignment();
                break;
            case ">>>=":
                result = factory.createUnsignedShiftRightAssignment();
                break;
            case "&=":
                result = factory.createBinaryAndAssignment();
                break;
            case "^=":
                result = factory.createBinaryXOrAssignment();
                break;
            case "|=":
                result = factory.createBinaryOrAssignment();
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + ctx.getText());
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitConditionalExpression(JavaKParser.ConditionalExpressionContext ctx) {
        if (ctx.COLON() == null) return accept(ctx.conditionalOrExpression());
        Operator op = factory.createConditional();
        Expression cond = accept(ctx.conditionalExpression());
        Expression e1 = accept(ctx.expression());
        Expression e2 = accept(ctx.conditionalOrExpression());
        ASTList<Expression> args = new ASTArrayList<Expression>(3);
        args.add(cond);
        args.add(e1);
        args.add(e2);
        op.setArguments(args);
        finish(op, ctx);
        return op;
    }

    @Override
    public Expression visitConditionalOrExpression(JavaKParser.ConditionalOrExpressionContext ctx) {
        Expression expr;
        Expression result = accept(ctx.conditionalAndExpression());
        if (ctx.conditionalOrExpression() == null) return result;
        Operator op = factory.createLogicalOr();
        expr = accept(ctx.conditionalOrExpression());

        ASTList<Expression> args = new ASTArrayList<Expression>(2);
        args.add(result);
        args.add(expr);
        op.setArguments(args);
        result = op;
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitConditionalAndExpression(JavaKParser.ConditionalAndExpressionContext ctx) {
        Operator op;
        Expression result = accept(ctx.inclusiveOrExpression());
        if (ctx.conditionalAndExpression() == null) return result;
        op = factory.createLogicalAnd();
        Expression expr = accept(ctx.conditionalAndExpression());

        ASTList<Expression> args = new ASTArrayList<Expression>(2);
        args.add(result);
        args.add(expr);
        op.setArguments(args);
        result = op;
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitInclusiveOrExpression(JavaKParser.InclusiveOrExpressionContext ctx) {
        Expression result;
        Expression expr;
        Operator op;

        result = accept(ctx.exclusiveOrExpression());
        if (ctx.inclusiveOrExpression() == null) return result;

        op = factory.createBinaryOr();
        expr = accept(ctx.inclusiveOrExpression());

        ASTList<Expression> args = new ASTArrayList<Expression>(2);
        args.add(result);
        args.add(expr);
        op.setArguments(args);
        result = op;
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitExclusiveOrExpression(JavaKParser.ExclusiveOrExpressionContext ctx) {
        Expression result = accept(ctx.andExpression());
        if (ctx.exclusiveOrExpression() == null) {
            return result;
        }

        Operator op = factory.createBinaryXOr();
        Expression expr = accept(ctx.exclusiveOrExpression());
        ASTList<Expression> args = new ASTArrayList<Expression>(2);
        args.add(result);
        args.add(expr);
        op.setArguments(args);
        result = op;
        setPostfixInfo(result, ctx);
        return result;
    }

    @Override
    public Expression visitAndExpression(JavaKParser.AndExpressionContext ctx) {
        Expression result;
        Expression expr;
        Operator op;

        result = accept(ctx.equalityExpression());
        if (ctx.andExpression() == null) return result;
        op = factory.createBinaryAnd();
        expr = accept(ctx.andExpression());
        ASTList<Expression> args = new ASTArrayList<Expression>(2);
        args.add(result);
        args.add(expr);
        op.setArguments(args);
        result = op;

        checkConstruction(result);
        setPostfixInfo(result, ctx);
        return result;
    }

    @Override
    public Expression visitEqualityExpression(JavaKParser.EqualityExpressionContext ctx) {
        Operator cmp;
        Expression a = accept(ctx.equalityExpression());
        Expression b = expect(ctx.relationalExpression());
        if (a == null) return b;
        if (ctx.EQUAL() != null) {
            cmp = factory.createEquals();
        } else {
            cmp = factory.createNotEquals();
        }
        ASTList<Expression> args = new ASTArrayList<Expression>(2);
        args.add(a);
        args.add(b);
        cmp.setArguments(args);
        finish(cmp, ctx);
        return cmp;
    }

    public Expression visitInstanceOfExpression(JavaKParser.RelationalExpressionContext ctx) {
        TypeReference tr;
        Expression result = accept(ctx.relationalExpression());
        tr = accept(ctx.referenceType());
        result = factory.createInstanceof(result, tr);
        setPrefixInfo(result, ctx);
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitRelationalExpression(JavaKParser.RelationalExpressionContext ctx) {
        if (ctx.relationalExpression() == null) {
            return accept(ctx.shiftExpression());
        }

        Operator cmp = null;
        if (ctx.LT() != null) {
            cmp = factory.createLessThan();
        } else if (ctx.GT() != null) {
            cmp = factory.createGreaterThan();
        } else if (ctx.LE() != null) {
            cmp = factory.createLessOrEquals();
        } else if (ctx.GE() != null) {
            cmp = factory.createGreaterOrEquals();
        }

        ASTList<Expression> args = new ASTArrayList<Expression>(2);
        args.add(accept(ctx.relationalExpression()));
        args.add(accept(ctx.shiftExpression()));
        assert cmp != null;
        cmp.setArguments(args);
        finish(cmp, ctx);
        return cmp;
    }

    @Override
    public Expression visitShiftExpression(JavaKParser.ShiftExpressionContext ctx) {
        Expression result;
        Operator shift = null;
        Expression expr;

        if (ctx.shiftExpression() == null) return accept(ctx.additiveExpression());
        if (ctx.LT().isEmpty()) {
            shift = factory.createShiftLeft();
        } else if (ctx.GT().size() == 2) {
            shift = factory.createShiftRight();
        } else if (ctx.GT().size() == 3) {
            shift = factory.createUnsignedShiftRight();
        }
        ASTList<Expression> args = new ASTArrayList<Expression>(2);
        args.add(accept(ctx.shiftExpression()));
        args.add(accept(ctx.additiveExpression()));
        shift.setArguments(args);
        result = shift;
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitAdditiveExpression(JavaKParser.AdditiveExpressionContext ctx) {
        Expression result;
        Operator add = null;
        Expression expr;

        if (ctx.ADD() != null) {
            add = factory.createPlus();
            setPrefixInfo(add, ctx);
        } else if (ctx.SUB() != null) {
            add = factory.createMinus();
            setPrefixInfo(add, ctx);
        }

        ASTList<Expression> args = new ASTArrayList<Expression>(2);
        args.add(accept(ctx.additiveExpression()));
        args.add(accept(ctx.multiplicativeExpression()));
        add.setArguments(args);
        result = add;
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitMultiplicativeExpression(JavaKParser.MultiplicativeExpressionContext ctx) {
        Expression result = null;
        Operator mult = null;
        Expression expr;
        if (ctx.multiplicativeExpression() == null) return accept(ctx.unaryExpression());
        if (ctx.MUL() != null) {
            mult = factory.createTimes();
            setPrefixInfo(mult, ctx);
        } else if (ctx.DIV() != null) {
            mult = factory.createDivide();
            setPrefixInfo(mult, ctx);
        } else if (ctx.MOD() != null) {
            mult = factory.createModulo();
            setPrefixInfo(mult, ctx);
        }
        ASTList<Expression> args = new ASTArrayList<Expression>(2);
        args.add(accept(ctx.multiplicativeExpression()));
        args.add(accept(ctx.unaryExpression()));
        mult.setArguments(args);
        result = mult;
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitUnaryExpression(JavaKParser.UnaryExpressionContext ctx) {
        Operator result;
        if (ctx.ADD() != null) {
            result = factory.createPositive();
        } else if (ctx.SUB() != null) {
            result = factory.createNegative();
        } else {
            return oneOf(ctx.preDecrementExpression(),
                    ctx.preIncrementExpression(),
                    ctx.unaryExpressionNotPlusMinus());
        }
        result.setArguments(new ASTArrayList<>((Expression) accept(ctx.unaryExpression())));
        /*result = ADTGetter() result = GeneralEscapExpression()*/
        finish(result, ctx);
        return result;
    }

    @Override
    public PreIncrement visitPreIncrementExpression(JavaKParser.PreIncrementExpressionContext ctx) {
        PreIncrement result = factory.createPreIncrement();
        Expression expr = accept(ctx.unaryExpression());
        result.setArguments(new ASTArrayList<>(expr));
        finish(result, ctx);
        return result;
    }

    @Override
    public PreDecrement visitPreDecrementExpression(JavaKParser.PreDecrementExpressionContext ctx) {
        PreDecrement result = factory.createPreDecrement();
        Expression expr = expect(ctx.unaryExpression());
        result.setArguments(new ASTArrayList<Expression>(expr));
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitUnaryExpressionNotPlusMinus(JavaKParser.UnaryExpressionNotPlusMinusContext ctx) {
        Operator result;
        if (ctx.TILDE() != null) {
            result = factory.createBinaryNot();
        } else if (ctx.BANG() != null) {
            result = factory.createLogicalNot();
        } else {
            return oneOf(ctx.postfixExpression(), ctx.castExpression());
        }

        result.setArguments(new ASTArrayList<>((Expression) accept(ctx.unaryExpression())));
        finish(result, ctx);
        return result;
    }


    @Override
    public Expression visitPostfixExpression(JavaKParser.PostfixExpressionContext ctx) {
        Expression result = oneOf(ctx.expressionName(), ctx.primary());
        for (Token child : ctx.post) {
            if (child.getType() == JavaKLexer.INC) {
                result = factory.createPostIncrement(result);
            } else {
                result = factory.createPostDecrement(result);
            }
        }
        finish(result, ctx);
        return result;
    }


    @Override
    public TypeCast visitCastExpression(JavaKParser.CastExpressionContext ctx) {
        TypeReference tr;
        Expression expr;
        TypeCast result = factory.createTypeCast();

        if (ctx.primitiveType() != null) {
            tr = accept(ctx.primitiveType());
            expr = accept(ctx.unaryExpression());
        } else if (ctx.referenceType() != null) {
            tr = accept(ctx.referenceType());
            //TODO additionalBound
            expr = accept(ctx.unaryExpressionNotPlusMinus());
        } else {
            throw new IllegalArgumentException("lambdas are unsupported");
        }
        result.setTypeReference(tr);
        result.setArguments(new ASTArrayList<>(expr));
        checkConstruction(result);
        setPostfixInfo(result, ctx);
        return result;
    }


    /*@Override
    public Expression visitPrimaryExpression(JavaKParser.PrimaryExpressionContext ctx) {
        Expression result = null;
        ReferencePrefix tmpResult = null;

        prefix = PrimaryPrefix()
        {
            // create initial AST construct from prefix only
            switch (prefix.type) {
                case PrimaryPrefixReturnValue.LITERAL:
                    if (prefix.literal instanceof StringLiteral) {
                        tmpResult = (StringLiteral) prefix.literal;
                    } else {
                        result = prefix.literal;
                        checkConstruction(result);
                        setPostfixInfo(result, ctx);
                        return result;
                        //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
                    }
                    break;
                case PrimaryPrefixReturnValue.THIS:
                    tmpResult = factory.createThisReference();
                    setPrefixInfo(tmpResult, ctx);
                    setPostfixInfo(tmpResult, ctx);
                    break;
                case PrimaryPrefixReturnValue.SUPER_MEMBER:
                    tmpResult = prefix.name;
                    break;
                case PrimaryPrefixReturnValue.PARENTHESIZED_EXPR:
                    tmpResult = (ParenthesizedExpression) prefix.expr;
                    break;
                case PrimaryPrefixReturnValue.ALLOCATION_EXPR:
                    tmpResult = (ReferencePrefix) prefix.expr;
                    break;
                case PrimaryPrefixReturnValue.CLASS_REF:
                    tmpResult = factory.createMetaClassReference(prefix.typeref);
                    setPrefixInfo(tmpResult, ctx);
                    setPostfixInfo(tmpResult, ctx);
                    break;
                case PrimaryPrefixReturnValue.QUALIFIED_NAME:
                    tmpResult = prefix.name;
                    break;
                case PrimaryPrefixReturnValue.PASSIVE_EXPR:
                    tmpResult = (PassiveExpression) prefix.expr;
                    break;
                case PrimaryPrefixReturnValue.ADT_CONSTRUCT:
                    tmpResult = (ADTPrefixConstruct) prefix.expr;
                    break;
                default:
                    throw new ParseException("Unknown prefix");
            }
        }
        (LOOKAHEAD(2) suffix = PrimarySuffix()
        {
            switch (suffix.type) {
                case PrimarySuffixReturnValue.THIS:
                    // the prefix MUST be a type expression!!!!!
                    // we currently only create UncollatedReferenceQualifiers
                    if (tmpResult instanceof TypeReference) {
                        tmpResult =
                                factory.createThisReference((TypeReference) tmpResult);
                        setPrefixInfo(tmpResult, ctx);
                        setPostfixInfo(tmpResult, ctx);
                    } else if (tmpResult instanceof UncollatedReferenceQualifier) {
                        tmpResult =
                                factory.createThisReference(((UncollatedReferenceQualifier) tmpResult).toTypeReference());
                        setPrefixInfo(tmpResult, ctx);
                        setPostfixInfo(tmpResult, ctx);
                    } else {
                        throw new ParseException("No type as prefix of `this'");
                    }
                    break;
                case PrimarySuffixReturnValue.SUPER:
                    // the prefix MUST be a type expression!!!!!
                    // we currently only create UncollatedReferenceQualifiers
                    if (tmpResult instanceof TypeReference) {
                        tmpResult =
                                factory.createSuperReference((TypeReference) tmpResult);
                        setPrefixInfo(tmpResult, ctx);
                        setPostfixInfo(tmpResult, ctx);
                    } else if (tmpResult instanceof UncollatedReferenceQualifier) {
                        tmpResult =
                                factory.createSuperReference(((UncollatedReferenceQualifier) tmpResult).toTypeReference());
                        setPrefixInfo(tmpResult, ctx);
                        setPostfixInfo(tmpResult, ctx);
                    } else if (tmpResult instanceof ThisReference) {
                        tmpResult =
                                factory.createSuperReference((ThisReference) tmpResult);
                        setPrefixInfo(tmpResult, ctx);
                        setPostfixInfo(tmpResult, ctx);
                    } else {
                        throw new ParseException("No type as prefix of `super', was " + tmpResult.getClass());
                    }
                    break;
                case PrimarySuffixReturnValue.ALLOCATION_EXPR:
                    if (suffix.expr instanceof New) {
                        ((New) suffix.expr).setReferencePrefix(tmpResult);
                        tmpResult = (New) suffix.expr;
                    } else {
                        throw new ParseException("Allocation without new?");
                    }
                    break;
                case PrimarySuffixReturnValue.INDEX_EXPR:
                    // suffix is either array / sequence access or subsequence construction
                    if (tmpResult instanceof UncollatedReferenceQualifier ||
                            tmpResult instanceof MethodReference ||
                            tmpResult instanceof ParenthesizedExpression ||
                            //tmpResult instanceof ThisReference || // this[i] in array initialization
                            tmpResult instanceof ADTPrefixConstruct ||
                            tmpResult instanceof VariableReference) {
                        if (suffix.expr instanceof RangeExpression) {
                            System.out.println("sucess! " + suffix.expr + " is a range"); // XXX
                            // XXX what if prefix ist Uncollated ???
                            tmpResult = new SeqSub((ADTPrefixConstruct) tmpResult, (RangeExpression) suffix.expr);
                        } else {
                            // Now we know that this is an array reference
                            ASTList<Expression> indicees = new ASTArrayList<Expression>(1);
                            indicees.add(suffix.expr);
                            tmpResult =
                                    factory.createArrayReference(tmpResult, indicees);
                            setPrefixInfo(tmpResult, ctx);
                            setPostfixInfo(tmpResult, ctx);
                        }
                    } else if (tmpResult instanceof ArrayReference) {
                        // we need to add another access dimension
                        ((ArrayReference) tmpResult).getDimensionExpressions().add(suffix.expr);
                    } else {
                        throw new ParseException("Bad index context - " +
                                tmpResult.getClass().getName() + "?!");
                    break;
                            case PrimarySuffixReturnValue.IDENTIFIER:
                            tmpResult=factory.createUncollatedReferenceQualifier(tmpResult,suffix.id);
                            ((UncollatedReferenceQualifier)tmpResult).setTypeArguments(suffix.typeArgs);
                            suffix.typeArgs=null;
                            setPrefixInfo(tmpResult,ctx);
                            setPostfixInfo(tmpResult,ctx);
                            break;
                            case PrimarySuffixReturnValue.ARGUMENTS:
                            // method call -determine the kind of method
                            if(tmpResult instanceof UncollatedReferenceQualifier){
                            // this is a normal method call
                            tmpResult=factory.createMethodReference
                            (((UncollatedReferenceQualifier)tmpResult).getReferencePrefix(),
                            ((UncollatedReferenceQualifier)tmpResult).getIdentifier(),
                            suffix.args,((UncollatedReferenceQualifier)tmpResult).getTypeArguments());

                            setPrefixInfo(tmpResult,ctx);
                            setPostfixInfo(tmpResult,ctx);
                            }else{
                            throw new ParseException("Arguments without method name?");
                            }
                            break;
default:
        throw new ParseException("Unknown primary suffix type");
        }
        }
        )*
        {
        if(tmpResult instanceof UncollatedReferenceQualifier){
        result=(UncollatedReferenceQualifier)tmpResult;
        // should be a FieldReference?
        }else{
        result=(Expression)tmpResult;
        }
        checkConstruction(result);
        setPostfixInfo(result,ctx);
        return result;
        }
        }
    */

    /*@Override
    public PrimaryPrefixReturnValue visitPrimaryPrefix(JavaKParser.PrimaryPrefixContext ctx) {
        // reuses global prefix field
        Literal lit;
        Expression expr;
        TypeReference tr;
        UncollatedReferenceQualifier qn;
        SuperReference supRef = null;
        ParenthesizedExpression parExpr = null;
        Identifier id = null;
        int dimension = 0;

        (
//  LOOKAHEAD(NonWildcardTypeArguments() "this" Arguments())
//  	NonWildcardTypeArguments() "this"  Arguments() is a mandatory suffix here!
        lit=Literal()
        {
        prefix.type=PrimaryPrefixReturnValue.LITERAL;
        prefix.literal=lit;
        }
        |
        "this"
        {
        prefix.type=PrimaryPrefixReturnValue.THIS;
        }
        |
        //[NonWildcardTypeArguments()]
        "super"{
        supRef=factory.createSuperReference();
        setPrefixInfo(supRef,ctx);
        setPostfixInfo(supRef,ctx);
        }
        "."
        id=ShortName()
        {
        setPrefixInfo(id,ctx);
        setPostfixInfo(id,ctx);
        prefix.name=
        factory.createUncollatedReferenceQualifier(supRef,id);
        prefix.type=PrimaryPrefixReturnValue.SUPER_MEMBER;
        }
        |

        {
        parExpr=factory.createParenthesizeExpression();
        setPrefixInfo(parExpr,ctx);
        }
        expr=Expression()

        {
        setPostfixInfo(parExpr,ctx);
        parExpr.setArguments(new ASTArrayList<Expression>(expr));
        prefix.expr=parExpr;
        prefix.type=PrimaryPrefixReturnValue.PARENTHESIZED_EXPR;
        }
        |
        "@("
        {
        parExpr=factory.createPassivExpression();
        setPrefixInfo(parExpr,ctx);
        }
        expr=accept(ctx.expression())

        {
        parExpr.setArguments(new ASTArrayList<Expression>(expr));
        prefix.expr=parExpr;
        prefix.type=PrimaryPrefixReturnValue.PASSIVE_EXPR;
        }
        |
        expr=AllocatioExpression()
        {
        prefix.type=PrimaryPrefixReturnValue.ALLOCATION_EXPR;
        prefix.expr=expr;
        }
        |
        LOOKAHEAD(ResultType()".""class")
        tr=ResultType()".""class"
        {
        prefix.type=PrimaryPrefixReturnValue.CLASS_REF;
        prefix.typeref=tr;
        }
        |
        qn=Name()
        {
        prefix.type=PrimaryPrefixReturnValue.QUALIFIED_NAME;
        prefix.name=qn;
        }
        |
        expr=ADTConstructor()
        {
        // XXX now primary expression (otherwise could not use expressions like \seq_reverse(x).length
        prefix.type=PrimaryPrefixReturnValue.ADT_CONSTRUCT;
        prefix.expr=expr;
        }
        )
        {
        return prefix;
        }
        }
        */
    /*
    @Override
    public Expression visitADTConstructor(JavaKParser.ADTConstructorContext ctx) {
        Expression result;
        Expression expr, expr2;

        (
                "\\singleton"  expr = accept(ctx.expression()) 
        {
            result = new Singleton(expr);
            setPrefixInfo(result, ctx);
        }
    |
        "\\set_union"  expr = accept(ctx.expression()) "," result = accept(ctx.expression()) 
        {
            result = new SetUnion(expr, result);
            setPrefixInfo(result, ctx);
        }
    |
        "\\intersect"  expr = accept(ctx.expression()) "," result = accept(ctx.expression()) 
        {
            result = new Intersect(expr, result);
            setPrefixInfo(result, ctx);
        }
    |
        "\\set_minus"  expr = accept(ctx.expression()) "," result = accept(ctx.expression()) 
        {
            result = new SetMinus(expr, result);
            setPrefixInfo(result, ctx);
        }
    |
        "\\all_fields"  expr = accept(ctx.expression()) 
        {
            result = new AllFields(expr);
            setPrefixInfo(result, ctx);
        }
    |
        "\\all_objects"  expr = accept(ctx.expression()) 
        {
            result = new AllObjects(expr);
            setPrefixInfo(result, ctx);
        }
    |
        "\\seq_singleton"  expr = accept(ctx.expression()) 
        {
            result = new SeqSingleton(expr);
            setPrefixInfo(result, ctx);
        }
    |
        "\\seq_concat"  expr = accept(ctx.expression()) "," result = accept(ctx.expression()) 
        {
            result = new SeqConcat(expr, result);
            setPrefixInfo(result, ctx);
        }
    |
        "\\seq_sub"  expr = accept(ctx.expression()) "," expr2 = accept(ctx.expression()) "," result = accept(ctx.expression()) 
        {
            result = new SeqSub(expr, expr2, result);
            setPrefixInfo(result, ctx);
        }
    |
        "\\seq_reverse"  expr = accept(ctx.expression()) 
        {
            result = new SeqReverse(expr);
            setPrefixInfo(result, ctx);
        }
    |
        "\\seq_put"  expr = accept(ctx.expression()) "," expr2 = accept(ctx.expression()) "," result = accept(ctx.expression()) 
        {
            // desugaring
            final Expression one = factory.createIntLiteral(1);
            final Expression first = new SeqSub(expr, factory.createIntLiteral(0), factory.createMinus(expr2, one));
            final Expression second = new SeqSingleton(result);
            final Expression third = new SeqSub(expr, factory.createPlus(expr2, one), factory.createMinus(new SeqLength(expr), one));
            result = new SeqConcat(first, new SeqConcat(second, third));
            setPrefixInfo(result, ctx);
        }
    )
        {
            checkConstruction(result);
            setPostfixInfo(result, ctx);
            return result;
        }
    }
*/

    @Override
    public Expression visitGeneralEscapeExpression(JavaKParser.GeneralEscapeExpressionContext ctx) {
        TerminalNode t = ctx.DL_EMBEDDED_FUNCTION() != null ? ctx.DL_EMBEDDED_FUNCTION() : ctx.MAP_FUNCTION();
        List<Expression> arguments = mapOf(ctx.expression());
        EscapeExpression result = EscapeExpression.getEscapeExpression(t.getText(), arguments);
        finish(result, ctx);
        return result;
    }
/*
@Override
public PrimarySuffixReturnValue visitPrimarySuffix(JavaKParser.PrimarySuffixContext ctx){
        // reuses global suffix field
        Expression expr;
        ASTList<Expression> args;
        Identifier id;
        Literal lit;
        ASTList<TypeArgumentDeclaration> typeArgs;

        (
//        //XXX it causes several warnings about nondeterminism. can those be ignored?
//  LOOKAHEAD(2)
//  ".." expr = accept(ctx.expression())
//  {
//      // subsequence range expression
//      suffix.type = PrimarySuffixReturnValue.RANGE;
//      suffix.expr = expr;
//  }
//|
        LOOKAHEAD(2)
        ".""this"
        {
        suffix.type=PrimarySuffixReturnValue.THIS;
        }
        |
        LOOKAHEAD(2,{isSuperAllowed()})
        ".""super"
        {
        suffix.type=PrimarySuffixReturnValue.SUPER;
        }
        |
        LOOKAHEAD(2)
        "."expr=AllocatioExpression()
        {
        suffix.type=PrimarySuffixReturnValue.ALLOCATION_EXPR;
        suffix.expr=expr;
        }
        |
//  LOOKAHEAD(3) // explicit Generic method invocation
        LOOKAHEAD(NonWildcardTypeArguments()ShortName()) // due to implicit indentifiers
        "."
        suffix.typeArgs=NonWildcardTypeArguments()suffix.id=ShortName()
        {
        suffix.type=suffix.IDENTIFIER;
        }
        |
        expr=IndexRange()
        {
        // can be simple array access, or subsequence construction
        suffix.type=PrimarySuffixReturnValue.INDEX_EXPR;
        suffix.expr=expr;
        }
        |
        "."

        suffix.id=ShortName()
        {
        suffix.type=PrimarySuffixReturnValue.IDENTIFIER;
        }
        |
        args=Arguments()
        {
        suffix.type=PrimarySuffixReturnValue.ARGUMENTS;
        suffix.args=args;
        }
        )
        {
        return suffix;
        }
        }
*/

    @Override
    public Literal visitLiteral(JavaKParser.LiteralContext ctx) {
        String text = ctx.getText();
        Literal result = null;
        if (ctx.IntegerLiteral() != null) {
            if (text.endsWith("L") || text.endsWith("l")) {
                result = factory.createLongLiteral(text);
            } else {
                result = factory.createIntLiteral(text);
            }
        } else if (ctx.FloatingPointLiteral() != null) {
            if (text.endsWith("F") || text.endsWith("f")) {
                result = factory.createFloatLiteral(text);
            } else {
                result = factory.createDoubleLiteral(text);
            }
        } else if (ctx.CharacterLiteral() != null) {
            result = factory.createCharLiteral(text);
        } else if (ctx.StringLiteral() != null)
            result = factory.createStringLiteral(text);
        else if (ctx.BooleanLiteral() != null) {
            result = factory.createBooleanLiteral(Boolean.parseBoolean(text));
        } else if (ctx.NullLiteral() != null) {
            result = factory.createNullLiteral();
        } else if (ctx.EMPTYSETLITERAL() != null) {
            result = EmptySetLiteral.INSTANCE;
            return result;
        } else if (ctx.EMPTYSEQLITERAL() != null) {
            result = EmptySeqLiteral.INSTANCE;
            return result;
        } else if (ctx.EMPTYMAPLITERAL() != null) {
            result = EmptyMapLiteral.INSTANCE;
            return result;
        }
        assert result != null;
        finish(result, ctx);
        return result;
    }

/*    @Override
    public ASTList<Expression> visitArguments(JavaKParser.ArgumentsContext ctx) {
        ASTList<Expression> result = null;
        [result = ArgumentList()] 
        {
            // !!! should set end coordinates to parent, possibly
            if (result != null) {
                checkConstruction(result);

            }
            return result;
        }
    }
*/

    @Override
    public ASTList<Expression> visitArgumentList(JavaKParser.ArgumentListContext ctx) {
        return mapOf(ctx.expression());
    }

    /*@Override
    public TypeOperator visitAllocationExpression(JavaKParser.AllocationExpressionContext ctx) {
        UncollatedReferenceQualifier qn;
        TypeOperator result;
        TypeReference tr;
        ASTList<Expression> args;
        ASTList<MemberDeclaration> body = null;
        ClassDeclaration cd = null;
        NewArray na;
        ASTList<TypeArgumentDeclaration> typeArgs;

        (
                LOOKAHEAD(2)
        "new"
        {
            na = factory.createNewArray();
            setPrefixInfo(na, ctx);
        }
        tr = PrimitiveType()
        {
            na.setTypeReference(tr);
        }
        result = ArrayDimsAndInits(na)
                |
                "new"
        {
            result = factory.createNew();
            setPrefixInfo(result, ctx);
        }
        qn = TypedName()
                [typeArgs = NonWildcardTypeArguments() {
            qn.setTypeArguments(typeArgs);
        } ]
        (
                args = Arguments()
                        [
                        {
                                cd = factory.createClassDeclaration();
        setPrefixInfo(cd, ctx);
       }
        body = ClassBody()
        {
            cd.setMembers(body);
            setPostfixInfo(cd, ctx);
        }
     ]
        {
            result.setTypeReference(qn.toTypeReference());
            ((New) result).setArguments(args);
            if (cd != null) {
                ((New) result).setClassDeclaration(cd);
            }
        }
   |
        {
            na = factory.createNewArray();
            copyPrefixInfo(result, na);
            na.setTypeReference(qn.toTypeReference());
        }
        result = ArrayDimsAndInits(na)
  )
)
        {
            checkConstruction(result);
            setPostfixInfo(result, ctx);
            return result;
        }
    }
    */
    /*
    public NewArray visitArrayDimsAndInitsArray(NewArray result) {
        int dimensions = 0;
        Expression expr;
        ASTList<Expression> sizes = null;
        ArrayInitializer init = null;

        (
                LOOKAHEAD(2)
        (LOOKAHEAD(2)
         expr =Expression()
        {
            sizes = (sizes == null) ? new ASTArrayList<Expression>() : sizes;
            sizes.add(expr);
            dimensions++;
        }
    )+
                (LOOKAHEAD(2)
         
        {
            dimensions++;
        }
    )*
|
        ( 
        {
            dimensions++;
        }
  )+
                init = ArrayInitializer()
)
        {
            //      setPrefixInfo(result);
            result.setDimensions(dimensions);
            if (sizes != null) {
                result.setArguments(sizes);
            }
            result.setArrayInitializer(init);
            checkConstruction(result);
            setPostfixInfo(result, ctx);
            return result;
        }
    }
    */

    @Override
    public Statement visitCatchAllStatement(JavaKParser.CatchAllStatementContext ctx) {
        UncollatedReferenceQualifier qn = expect(ctx.qn);
        StatementBlock block = expect(ctx.block());
        Statement result = factory.createCatchAllStatement(qn.toVariableReference(), block);
        finish(result, ctx);
        return result;
    }

    @Override
    public LabeledStatement visitLabeledStatement(JavaKParser.LabeledStatementContext ctx) {
        Identifier id = accept(ctx.identifier());
        Statement stat = accept(ctx.statement());
        LabeledStatement result = factory.createLabeledStatement();
        result.setIdentifier(id);
        result.setBody(stat);
        finish(result, ctx);
        return result;
    }

    @Override
    public MethodCallStatement visitMethodCallStatement(JavaKParser.MethodCallStatementContext ctx) {
        MethodCallStatement result;
        VariableReference resVar = null;
        UncollatedReferenceQualifier qn;
        StatementBlock block;
        ExecutionContext ec;
        if (ctx.identifier() != null) {
            qn = expect(ctx.identifier());
            resVar = qn.toVariableReference();
        }
        ec = expect(ctx.executionContext());
        block = expect(ctx.block());
        result = factory.createMethodCallStatement(resVar, ec, block);
        finish(result, ctx);
        return result;
    }

    @Override
    public MethodBodyStatement visitMethodBodyStatement(JavaKParser.MethodBodyStatementContext ctx) {
        VariableReference resVar = null;
        if (ctx.identifier() != null) {
            UncollatedReferenceQualifier qn = expect(ctx.identifier());
            resVar = qn.toVariableReference();
        }
        Expression tmp = accept(ctx.expression());
        TypeReference bodySource = accept(ctx.unannType());
        MethodBodyStatement result;
        MethodReference methRef;
        if (tmp instanceof MethodReference) {
            methRef = (MethodReference) tmp;
            result = factory.createMethodBodyStatement(bodySource, resVar, methRef);
        } else {
            throw new RuntimeException("Expected a method reference.");
            //result = factory.createMethodBodyStatement(bodySource, resVar, methRef);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public ExecutionContext visitExecutionContext(JavaKParser.ExecutionContextContext ctx) {
        MethodSignature methodSignature = accept(ctx.methodDeclarator());
        TypeReference classContext = accept(ctx.unannType());
        Expression runtimeInstance = accept(ctx.expression());
        return new ExecutionContext(classContext, methodSignature,
                (ReferencePrefix) runtimeInstance);
    }

    @Override
    public Object visitMethodDeclarator(JavaKParser.MethodDeclaratorContext ctx) {
        ASTList<TypeReference> paramTypes = new ASTArrayList<TypeReference>();
        UncollatedReferenceQualifier name = expect(ctx.identifier());
        //TODO paramTypes ctx.formalParameterList()
        return factory.createMethodSignature(name.getIdentifier(), paramTypes);
    }

    @Override
    public StatementBlock visitBlock(JavaKParser.BlockContext ctx) {
        return accept(ctx.blockStatements());
    }

    @Override
    public StatementBlock visitBlockStatements(JavaKParser.BlockStatementsContext ctx) {
        StatementBlock result = factory.createStatementBlock();
        ASTList<Statement> sl = new ASTArrayList<>();
        for (JavaKParser.BlockStatementContext context : ctx.blockStatement()) {
            sl.add((Statement) accept(context));
        }
        result.setBody(sl);
        finish(result, ctx);
        return result;
    }

    @Override
    public LocalVariableDeclaration visitLocalVariableDeclaration(JavaKParser.LocalVariableDeclarationContext ctx) {
        ASTList<VariableSpecification> vl = expect(ctx.variableDeclaratorList());
        ASTList<DeclarationSpecifier> declSpecs = mapOf(ctx.variableModifier());
        LocalVariableDeclaration result = factory.createLocalVariableDeclaration();
        if (declSpecs.size() != 0)
            result.setDeclarationSpecifiers(declSpecs);
        TypeReference tr = expect(ctx.unannType());
        result.setTypeReference(tr);
        result.setVariableSpecifications(vl);
        finish(result, ctx);
        return result;
    }

    @Override
    public ASTList<VariableSpecification> visitVariableDeclaratorList(JavaKParser.VariableDeclaratorListContext ctx) {
        return mapOf(ctx.variableDeclarator());
    }


    @Override
    public EmptyStatement visitEmptyStatement(JavaKParser.EmptyStatementContext ctx) {
        EmptyStatement result = factory.createEmptyStatement();
        finish(result, ctx);
        return result;
    }


    @Override
    public Switch visitSwitchStatement(JavaKParser.SwitchStatementContext ctx) {
        ASTList<Branch> branches = accept(ctx.switchBlock());
        Switch result = factory.createSwitch();
        Expression expr = accept(ctx.expression());
        result.setExpression(expr);
        result.setBranchList(branches);
        finish(result, ctx);
        return result;
    }

    @Override
    public ASTList<Branch> visitSwitchBlock(JavaKParser.SwitchBlockContext ctx) {
        ASTList<Branch> branches = new ASTArrayList<>();
        for (JavaKParser.SwitchBlockStatementGroupContext b : ctx.switchBlockStatementGroup()) {
            branches.add(accept(b));
        }
        if (!ctx.switchLabel().isEmpty()) {
            //maybe todo
        }
        return branches;
    }

    @Override
    public Object visitSwitchBlockStatementGroup(JavaKParser.SwitchBlockStatementGroupContext ctx) {
        if (ctx.switchLabels().switchLabel().size() != 1) {
            throw new IllegalStateException();
        }
        Branch result = expect(ctx.switchLabels().switchLabel(0));
        ASTList<Statement> body = accept(ctx.blockStatements());
        if (result instanceof Case) {
            ((Case) result).setBody(body);
        } else {
            ((Default) result).setBody(body);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Branch visitSwitchLabel(JavaKParser.SwitchLabelContext ctx) {
        // handle ctx.enumConstantName()
        if (ctx.CASE() != null) {
            Case result = factory.createCase();
            Expression expr = expect(ctx.constantExpression());
            result.setExpression(expr);
            return result;
        } else {
            return factory.createDefault();
        }
    }

    @Override
    public Assert visitAssertStatement(JavaKParser.AssertStatementContext ctx) {
        Expression msg = null;
        Assert result = factory.createAssert();
        Expression cond = expect(ctx.expression(0));
        if (ctx.expression().size() == 2) {
            msg = accept(ctx.expression(1));
        }
        result.setCondition(cond);
        result.setMessage(msg);
        finish(result, ctx);
        return result;
    }


    @Override
    public Object visitIfThenStatement(JavaKParser.IfThenStatementContext ctx) {
        If result = factory.createIf();
        Expression cond = accept(ctx.expression());
        Then thenStat = factory.createThen();
        Statement trueStat = accept(ctx.statement());
        thenStat.setBody(trueStat);
        result.setExpression(cond);
        result.setThen(thenStat);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitIfThenElseStatement(JavaKParser.IfThenElseStatementContext ctx) {
        If result = factory.createIf();
        Expression cond = accept(ctx.expression());
        Then thenStat = factory.createThen();
        Statement trueStat = accept(ctx.statementNoShortIf());
        thenStat.setBody(trueStat);
        Else elseStat = factory.createElse();
        setPrefixInfo(elseStat, ctx);
        Statement falseStat = accept(ctx.statement());
        elseStat.setBody(falseStat);
        result.setExpression(cond);
        result.setThen(thenStat);
        result.setElse(elseStat);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitIfThenElseStatementNoShortIf(JavaKParser.IfThenElseStatementNoShortIfContext ctx) {
        If result = factory.createIf();
        Expression cond = accept(ctx.expression());
        Then thenStat = factory.createThen();
        Statement trueStat = accept(ctx.statementNoShortIf(0));
        thenStat.setBody(trueStat);
        Else elseStat = factory.createElse();
        setPrefixInfo(elseStat, ctx);
        Statement falseStat = accept(ctx.statementNoShortIf(1));
        elseStat.setBody(falseStat);
        result.setExpression(cond);
        result.setThen(thenStat);
        result.setElse(elseStat);
        finish(result, ctx);
        return result;

    }

    @Override
    public While visitWhileStatement(JavaKParser.WhileStatementContext ctx) {
        Expression expr = accept(ctx.expression());
        Statement stat = accept(ctx.statement());
        While result = factory.createWhile();
        result.setGuard(expr);
        result.setBody(stat);
        finish(result, ctx);
        return result;
    }

    @Override
    public Do visitDoStatement(JavaKParser.DoStatementContext ctx) {
        Do result = factory.createDo();
        Expression expr = accept(ctx.expression());
        Statement stat = accept(ctx.statement());
        result.setGuard(expr);
        result.setBody(stat);
        finish(result, ctx);
        return result;
    }

    @Override
    public LoopStatement visitBasicForStatement(JavaKParser.BasicForStatementContext ctx) {
        LoopStatement result;
        ASTList<LoopInitializer> init = accept(ctx.forInit());
        Expression guard = null;
        ASTList<Expression> update = null;
        Statement body;
        result = factory.createFor();
        guard = accept(ctx.expression());
        update = accept(ctx.forUpdate());
        body = accept(ctx.statement());

        result.setInitializers(init);
        result.setGuard(guard);
        result.setUpdates(update);
        result.setBody(body);
        finish(result, ctx);
        return result;

    }

    @Override
    public EnhancedFor visitEnhancedForStatement(JavaKParser.EnhancedForStatementContext ctx) {
        EnhancedFor result = factory.createEnhancedFor();
        @NotNull ASTList<LoopInitializer> init = expect(ctx.variableDeclaratorId());
        @NotNull Expression guard = expect(ctx.expression());
        @NotNull Statement body = expect(ctx.statement());
        result.setBody(body);
        result.setInitializers(init);
        result.setGuard(guard);
        finish(result, ctx);
        return result;
    }

    @Override
    public ASTList<LoopInitializer> visitForInit(JavaKParser.ForInitContext ctx) {
        ASTList<LoopInitializer> result = new ASTArrayList<LoopInitializer>();
        ASTList<Expression> exprs = null;
        ASTList<LocalVariableDeclaration> varDecl = accept(ctx.localVariableDeclaration());
        if (varDecl != null) {
            //TODO result.add(varDecl);
        } else {
            for (int i = 0, s = exprs.size(); i < s; i += 1)
                result.add((LoopInitializer) exprs.get(i));
        }
        return result;
    }


    @Override
    public ASTList<Expression> visitStatementExpressionList(JavaKParser.StatementExpressionListContext ctx) {
        return mapOf(ctx.statementExpression());
    }

    @Override
    public ASTList<Expression> visitForUpdate(JavaKParser.ForUpdateContext ctx) {
        return accept(ctx.statementExpressionList());
    }

    @Override
    public TransactionStatement visitTransactionStatement(JavaKParser.TransactionStatementContext ctx) {
        String name = ctx.getText();
        int type = 0;
        if (name.equals("#begin")) {
            type = TransactionStatement.BEGIN;
        } else if (name.equals("#commit")) {
            type = TransactionStatement.COMMIT;
        } else if (name.equals("#finish")) {
            type = TransactionStatement.FINISH;
        } else if (name.equals("#abort")) {
            type = TransactionStatement.ABORT;
        }
        return new TransactionStatement(type);
    }


    @Override
    public Break visitBreakStatement(JavaKParser.BreakStatementContext ctx) {
        Break result = factory.createBreak();
        Identifier id = accept(ctx.identifier());
        result.setIdentifier(id);
        finish(result, ctx);
        return result;
    }

    @Override
    public Continue visitContinueStatement(JavaKParser.ContinueStatementContext ctx) {
        Continue result = factory.createContinue();
        Identifier id = accept(ctx.identifier());
        result.setIdentifier(id);
        finish(result, ctx);
        return result;
    }

    @Override
    public Return visitReturnStatement(JavaKParser.ReturnStatementContext ctx) {
        Return result = factory.createReturn();
        Expression expr = accept(ctx.expression());
        result.setExpression(expr);
        checkConstruction(result);
        finish(result, ctx);
        return result;
    }

    @Override
    public Throw visitThrowStatement(JavaKParser.ThrowStatementContext ctx) {
        Throw result = factory.createThrow();
        Expression expr = accept(ctx.expression());
        result.setExpression(expr);
        finish(result, ctx);
        return result;
    }

    @Override
    public SynchronizedBlock visitSynchronizedStatement(JavaKParser.SynchronizedStatementContext ctx) {
        SynchronizedBlock result;
        Expression expr;
        StatementBlock block;
        result = factory.createSynchronizedBlock();
        expr = accept(ctx.expression());
        block = accept(ctx.block());
        result.setExpression(expr);
        result.setBody(block);
        finish(result, ctx);
        return result;
    }

    @Override
    public LoopScopeBlock visitLoopScope(JavaKParser.LoopScopeContext ctx) {
        LoopScopeBlock result = factory.createLoopScopeBlock();
        Expression indexPV = accept(ctx.expression());
        StatementBlock block = accept(ctx.block());
        result.setIndexPV(indexPV);
        result.setBody(block);
        finish(result, ctx);
        return result;
    }

    @Override
    public MergePointStatement visitMergePointStatement(JavaKParser.MergePointStatementContext ctx) {
        MergePointStatement result = factory.createMergePointStatement();
        Expression expr = accept(ctx.expression());
        result.setIndexPV(expr);
        finish(result, ctx);
        return result;
    }

    @Override
    public Try visitTryStatement(JavaKParser.TryStatementContext ctx) {
        ASTList<Branch> branches = new ASTArrayList<Branch>(1);
        Try result = factory.createTry();
        StatementBlock block = expect(ctx.block());
        result.setBody(block);
        List<Catch> catches = accept(ctx.catches());
        finish(result, ctx);
        return result;
    }

    @Override
    public List<Catch> visitCatches(JavaKParser.CatchesContext ctx) {
        return mapOf(ctx.catchClause());
    }

    @Override
    public Finally visitFinally_(JavaKParser.Finally_Context ctx) {
        Finally result = factory.createFinally();
        Statement block = accept(ctx.block());
        result.setBody(block);
        finish(result, ctx);
        return result;
    }

    @Override
    public Catch visitCatchClause(JavaKParser.CatchClauseContext ctx) {
        Catch cat = factory.createCatch();
        ParameterDeclaration param = accept(ctx.catchFormalParameter());
        Statement block = expect(ctx.block());
        cat.setParameterDeclaration(param);
        cat.setBody(block);
        finish(cat, ctx);
        return cat;
    }

    @Override
    public ParameterDeclaration visitCatchFormalParameter(JavaKParser.CatchFormalParameterContext ctx) {
        TypeReference type = accept(ctx.catchType());
        ASTList<DeclarationSpecifier> mods = mapOf(ctx.variableModifier());
        @NotNull Identifier id = expect(ctx.variableDeclaratorId());
        ParameterDeclaration result = new ParameterDeclaration(mods, type, id);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitCatchType(JavaKParser.CatchTypeContext ctx) {
        return expect(ctx.unannClassType());
    }

    @Override
    public Exec visitExecStatement(JavaKParser.ExecStatementContext ctx) {
        ParameterDeclaration param;
        ASTList<Branch> branches = mapOf(ctx.ccatchBlock());
        Exec result = factory.createExec();
        StatementBlock block = accept(ctx.block());
        result.setBody(block);
        result.setBranchList(branches);
        result.setBranchList(branches);
        checkConstruction(result);
        setPostfixInfo(result, ctx);
        return result;
    }

    @Override
    public Object visitCcatchBlock(JavaKParser.CcatchBlockContext ctx) {
        Ccatch cat = factory.createCcatch();
        Statement block = expect(ctx.block());
        cat.setBody(block);

        if (ctx.identifier() != null) {
            Identifier id = expect(ctx.identifier());
            if (ctx.RETURNTYPE() != null) {
                assert false;
            } else if (ctx.BREAKTYPE() != null) {
                cat.setNonStdParameterDeclaration(factory.createCcatchBreakLabelParameterDeclaration(id));
            } else if (ctx.CONTINUETYPE() != null) {
                cat.setNonStdParameterDeclaration(factory.createCcatchContinueLabelParameterDeclaration(id));
            }
        } else if (ctx.formalParameter() != null) {
            ParameterDeclaration param = accept(ctx.formalParameter());
            if (ctx.RETURNTYPE() != null) {
                cat.setNonStdParameterDeclaration(factory.createCcatchReturnValParameterDeclaration(param));
                cat.setParameterDeclaration(param);
            } else {
                assert false;
            }
        } else if (ctx.MUL() != null) {
            if (ctx.RETURNTYPE() != null) {
                assert false;
            } else if (ctx.BREAKTYPE() != null) {
                cat.setNonStdParameterDeclaration(factory.createCcatchBreakWildcardParameterDeclaration());
            } else if (ctx.CONTINUETYPE() != null) {
                cat.setNonStdParameterDeclaration(factory.createCcatchContinueWildcardParameterDeclaration());
            }
        } else {
            if (ctx.RETURNTYPE() != null) {
                cat.setNonStdParameterDeclaration(factory.createCcatchReturnParameterDeclaration());
            } else if (ctx.BREAKTYPE() != null) {
                cat.setNonStdParameterDeclaration(factory.createCcatchBreakParameterDeclaration());
            } else if (ctx.CONTINUETYPE() != null) {
                cat.setNonStdParameterDeclaration(factory.createCcatchContinueParameterDeclaration());
            }
        }

        return cat;
    }

    /*
    // Java 5 specific
    @Override
    public AnnotationUseSpecification visitAnnotationUse(JavaKParser.AnnotationUseContext ctx) {
        TypeReference tr;
        AnnotationUseSpecification result = factory.createAnnotationUseSpecification();
        Expression ev = null;
        ASTList<AnnotationElementValuePair> list = null;
        AnnotationPropertyReference id;
        AnnotationElementValuePair evp;

        "@"
        {
            setPrefixInfo(result, ctx);
        }
        tr = Type()
                [ {
            list = new ASTArrayList<AnnotationElementValuePair>();
        }
	    [
        LOOKAHEAD( < IDENTIFIER > "=")
				<IDENTIFIER > {
                id = factory.createAnnotationPropertyReference(token.image);
        setPrefixInfo(id, ctx);
        setPostfixInfo(id, ctx);
				}"=" ev = ElementValue()
        {
            evp = new AnnotationElementValuePair(id, ev);
            setPrefixInfo(evp, ctx);
            setPostfixInfo(evp, ctx);
            list.add(evp);
        }
        (
                "," < IDENTIFIER > {
                        id = factory.createAnnotationPropertyReference(token.image);
        setPrefixInfo(id, ctx);
        setPostfixInfo(id, ctx);
					 }"=" ev = ElementValue()
        {
            evp = new AnnotationElementValuePair(id, ev);
            setPrefixInfo(evp, ctx);
            setPostfixInfo(evp, ctx);
            list.add(evp);
        }
				)*
			|
        LOOKAHEAD(ElementValue())
        ev = ElementValue() {
            evp = new AnnotationElementValuePair(null, ev);
            setPrefixInfo(evp, ctx);
            setPostfixInfo(evp, ctx);
            list.add(evp);
        } // Single Element Annotation
		]
        
	]
        {
            result.setTypeReference(tr);
            if (list != null) {
                result.setElementValuePairs(list);
            }
            setPostfixInfo(result, ctx);
            return result;
        }
    }*/

    @Override
    public Expression visitElementValue(JavaKParser.ElementValueContext ctx) {
        return oneOf(ctx.annotation(), ctx.conditionalExpression(), ctx.elementValueArrayInitializer());
    }

    @Override
    public Identifier visitIdentifier(JavaKParser.IdentifierContext ctx) {
        Identifier result;
        if (ctx.ImplicitIdentifier() != null) {
            result = factory.createImplicitIdentifier(ctx.getText());
        } else {
            result = factory.createIdentifier(ctx.getText());
        }
        finish(result, ctx);
        return result;
    }
}

