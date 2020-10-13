package de.uka.ilkd.key.parser.njava;

import de.uka.ilkd.key.java.recoderext.*;
import de.uka.ilkd.key.java.recoderext.adt.*;
import de.uka.ilkd.key.nparser.JavaKBaseVisitor;
import de.uka.ilkd.key.nparser.JavaKParser;
import org.antlr.misc.IntArrayList;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import recoder.abstraction.TypeArgument;
import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.expression.*;
import recoder.java.expression.operator.Instanceof;
import recoder.java.expression.operator.NewArray;
import recoder.java.expression.operator.TypeCast;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import recoder.parser.ParseException;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import static java.lang.String.format;

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

    @Override
    public CompilationUnit visitCompilationUnit(JavaKParser.CompilationUnitContext ctx) {
        PackageSpecification ps = accept(ctx.packageDeclaration());
        if (ps == null) {
            ps = new PackageSpecification();
        }
        ASTList<Import> imports = mapOf(ctx.importDeclaration());
        ASTList<TypeDeclaration> tmp = mapOf(ctx.typeDeclaration());
        ASTList<TypeDeclaration> declarations = new ASTArrayList<>();
        for (TypeDeclaration typeDeclaration : tmp) {
            if(typeDeclaration!=null) declarations.add(typeDeclaration); //Remove empty declaration
        }
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
        UncollatedReferenceQualifier qn = accept(ctx.qualifiedName());
        result.setPackageReference(qn.toPackageReference());
        finish(result, ctx);
        return result;
    }


    @Override
    public UncollatedReferenceQualifier visitQualifiedName(JavaKParser.QualifiedNameContext ctx) {
        ASTList<Identifier> identifiers = mapOf(ctx.identifier());
        UncollatedReferenceQualifier result = null;
        for (Identifier identifier : identifiers) {
            if (result == null) {
                result = factory.createUncollatedReferenceQualifier(identifier);
            } else {
                result = factory.createUncollatedReferenceQualifier(result, identifier);
            }
        }
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
                result.setReference(qn.toTypeReference());
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

    protected DeclarationSpecifier getModifier(String s) {
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
    public Object visitClassOrInterfaceModifier(JavaKParser.ClassOrInterfaceModifierContext ctx) {
        if (ctx.annotation() != null) {
            return expect(ctx.annotation());
        }
        return getModifier(ctx.getText());
    }

    @Override
    public TypeDeclaration visitTypeDeclaration(JavaKParser.TypeDeclarationContext ctx) {
        try {
            TypeDeclaration td = oneOf(ctx.classDeclaration(),
                    ctx.enumDeclaration(),
                    ctx.interfaceDeclaration(),
                    ctx.annotationTypeDeclaration());
            ASTList<DeclarationSpecifier> modifier = mapOf(ctx.classOrInterfaceModifier());
            set(td, modifier);
            return td;
        } catch (IllegalArgumentException e) {
            return null;
        }
    }

    @Override
    public AnnotationDeclaration visitAnnotationTypeDeclaration(JavaKParser.AnnotationTypeDeclarationContext ctx) {
        ASTList<MemberDeclaration> members = new ASTArrayList<>();
        MethodDeclaration md;
        ASTList<DeclarationSpecifier> declSpecs = new ASTArrayList<>(), methodDs;
        AnnotationDeclaration result = new AnnotationDeclaration();
        Identifier name = accept(ctx.identifier());
        methodDs = new ASTArrayList<>();
        TypeReference methodRes = null;
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

    @Override
    public Object visitAnnotationTypeBody(JavaKParser.AnnotationTypeBodyContext ctx) {
        return mapOf(ctx.annotationTypeElementDeclaration());
    }

    @Override
    public MemberDeclaration visitAnnotationTypeElementDeclaration(JavaKParser.AnnotationTypeElementDeclarationContext ctx) {
        MemberDeclaration decl = expect(ctx.annotationTypeElementRest());
        ASTList<DeclarationSpecifier> modifier = mapOf(ctx.modifier());
        set(decl, modifier);
        finish(decl, ctx);
        return decl;
    }

    @Override
    public Object visitAnnotationTypeElementRest(JavaKParser.AnnotationTypeElementRestContext ctx) {
        if (ctx.typeType() != null) {
            /*     : typeType annotationMethodOrConstantRest ';'*/
            return null;
        } else
            return oneOf(ctx.classDeclaration(),
                    ctx.interfaceDeclaration(),
                    ctx.enumDeclaration(),
                    ctx.annotationTypeDeclaration());
    }

    @Override
    public EnumDeclaration visitEnumDeclaration(JavaKParser.EnumDeclarationContext ctx) {
        EnumDeclaration result = new EnumDeclaration();
        Identifier id = accept(ctx.identifier());
        result.setIdentifier(id);
        ASTList<TypeReference> interfaces = accept(ctx.typeList());
        if (interfaces != null) {
            Implements im = factory.createImplements();
            im.setSupertypes(interfaces);
            result.setImplementedTypes(im);
            finish(im, ctx);
        }
        ASTList<MemberDeclaration> members = new ASTArrayList<>();
        ASTList<MemberDeclaration> constants = accept(ctx.enumConstants());
        ASTList<MemberDeclaration> body = accept(ctx.enumBodyDeclarations());

        if (constants != null)
            members.addAll(constants);
        if (body != null)
            members.addAll(body);
        result.setMembers(members);
        finish(result, ctx);
        return result;
    }

    @Override
    public List<MemberDeclaration> visitEnumConstants(JavaKParser.EnumConstantsContext ctx) {
        return mapOf(ctx.enumConstant());
    }

    @Override
    public MemberDeclaration visitEnumConstant(JavaKParser.EnumConstantContext ctx) {
        ASTList<DeclarationSpecifier> annotations = mapOf(ctx.annotation());
        Identifier id = accept(ctx.identifier());
        ASTList<Expression> args = accept(ctx.arguments());
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
    public Object visitEnumBodyDeclarations(JavaKParser.EnumBodyDeclarationsContext ctx) {
        return mapOf(ctx.classBodyDeclaration());
    }

    @Override
    public ASTList<TypeParameterDeclaration> visitTypeParameters(JavaKParser.TypeParametersContext ctx) {
        return mapOf(ctx.typeParameter());
    }

    @Override
    public Object visitClassDeclaration(JavaKParser.ClassDeclarationContext ctx) {
        ClassDeclaration result = factory.createClassDeclaration();
        Identifier id = expect(ctx.identifier());
        result.setIdentifier(id);

        if (ctx.typeParameters() != null) {
            ASTList<TypeParameterDeclaration> typeParams = expect(ctx.typeParameters());
            result.setTypeParameters(typeParams);
        }

        if (ctx.EXTENDS() != null) {
            Extends ex = factory.createExtends();
            TypeReference tr = expect(ctx.typeType());
            ex.setSupertypes(new ASTArrayList<>(1));
            ex.getSupertypes().add(tr);
            result.setExtendedTypes(ex);
        }

        if (ctx.IMPLEMENTS() != null) {
            Implements im = factory.createImplements();
            ASTList<TypeReference> nl = expect(ctx.typeList());
            im.setSupertypes(nl);
            result.setImplementedTypes(im);
        }

        ASTList<MemberDeclaration> mdl = expect(ctx.classBody());
        result.setMembers(mdl);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitTypeList(JavaKParser.TypeListContext ctx) {
        return mapOf(ctx.typeType());
    }

    @Override
    public ASTList<MemberDeclaration> visitClassBody(JavaKParser.ClassBodyContext ctx) {
        return mapOf(ctx.classBodyDeclaration());
    }

    @Override
    public MemberDeclaration visitClassBodyDeclaration(JavaKParser.ClassBodyDeclarationContext ctx) {
        if (ctx.STATIC() != null) {
            //TODO static block
        } else if (ctx.memberDeclaration() != null) {
            List<DeclarationSpecifier> modifiers = mapOf(ctx.modifier());
            MemberDeclaration md = expect(ctx.memberDeclaration());
            set(md, modifiers);
            finish(md, ctx);
            return md;
        }
        return null; //empty declaration
    }

    private void set(Object md, List<DeclarationSpecifier> modifiers) {
        try {
            Method m = md.getClass().getMethod("setDeclarationSpecifiers", ASTList.class);
            m.invoke(md, modifiers);
        } catch (IllegalAccessException | InvocationTargetException | NoSuchMethodException ignored) {
            throw new RuntimeException(md.getClass() + " does not have setDeclarationSpecifiers");
        }
    }

    @Override
    public InterfaceDeclaration visitInterfaceDeclaration(JavaKParser.InterfaceDeclarationContext ctx) {
        InterfaceDeclaration result = new InterfaceDeclaration();
        Identifier id = accept(ctx.identifier());
        result.setIdentifier(id);
        if (ctx.typeParameters() != null) {
            ASTList<TypeParameterDeclaration> typeParams = expect(ctx.typeParameters());
            result.setTypeParameters(typeParams);
        }
        if (ctx.EXTENDS() != null) {
            Extends im = factory.createExtends();
            ASTList<TypeReference> nl = expect(ctx.typeList());
            im.setSupertypes(nl);
            result.setExtendedTypes(im);
        }
        result.setMembers(expect(ctx.interfaceBody()));
        finish(result, ctx);
        return result;
    }

    @Override
    public ASTList<MemberDeclaration> visitInterfaceBody(JavaKParser.InterfaceBodyContext ctx) {
        return mapOf(ctx.interfaceBodyDeclaration());
    }

    @Override
    public Object visitInterfaceBodyDeclaration(JavaKParser.InterfaceBodyDeclarationContext ctx) {
        ASTList<DeclarationSpecifier> modifiers = mapOf(ctx.modifier());
        MemberDeclaration result = expect(ctx.interfaceMemberDeclaration());
        set(result, modifiers);
        finish(result, ctx);
        return result;
    }

    @Override
    public MemberDeclaration visitInterfaceMemberDeclaration(JavaKParser.InterfaceMemberDeclarationContext ctx) {
        return oneOf(ctx.constDeclaration(), ctx.interfaceDeclaration(),
                ctx.genericInterfaceMethodDeclaration(), ctx.interfaceDeclaration(),
                ctx.annotationTypeDeclaration(), ctx.classDeclaration(),
                ctx.enumDeclaration());
    }

    @Override
    public Object visitConstDeclaration(JavaKParser.ConstDeclarationContext ctx) {
        ASTList<FieldSpecification> vl = mapOf(ctx.constantDeclarator());
        FieldDeclaration result = factory.createFieldDeclaration();
        TypeReference tr = expect(ctx.typeType());
        result.setTypeReference(tr);
        result.setFieldSpecifications(vl);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitConstantDeclarator(JavaKParser.ConstantDeclaratorContext ctx) {
        VariableSpecification result;
        Identifier id = accept(ctx.identifier());
        Expression init = accept(ctx.variableInitializer());
        int dim = ctx.LBRACK().size();
        if (isForField) {
            result = factory.createFieldSpecification(id, dim, init);
        } else {
            result = factory.createVariableSpecification(id, dim, init);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public FieldDeclaration visitFieldDeclaration(JavaKParser.FieldDeclarationContext ctx) {
        ASTArrayList<FieldSpecification> vl = expect(ctx.variableDeclarators());
        FieldDeclaration result = factory.createFieldDeclaration();
        TypeReference tr = expect(ctx.typeType());
        result.setTypeReference(tr);
        result.setFieldSpecifications(vl);
        finish(result, ctx);
        return result;
    }

    private boolean isForField = true;

    @Override
    public VariableSpecification visitVariableDeclarator(JavaKParser.VariableDeclaratorContext ctx) {
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
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitVariableInitializer(JavaKParser.VariableInitializerContext ctx) {
        return oneOf(ctx.expression(), ctx.arrayInitializer());
    }

    @Override
    public Identifier visitVariableDeclaratorId(JavaKParser.VariableDeclaratorIdContext ctx) {
        Identifier result = accept(ctx.identifier());
        tmpDimension = ctx.RBRACK().size();
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitArrayInitializer(JavaKParser.ArrayInitializerContext ctx) {
        ASTList<Expression> el = new ASTArrayList<>();
        ArrayInitializer result = factory.createArrayInitializer();
        List<Expression> init = mapOf(ctx.variableInitializer());
        init.forEach(it -> el.add(it));
        result.setArguments(el);
        finish(result, ctx);
        return result;
    }


    @Override
    public MethodDeclaration visitMethodDeclaration(JavaKParser.MethodDeclarationContext ctx) {
        MethodDeclaration result = new MethodDeclaration();
        StatementBlock body;
        ASTList<TypeParameterDeclaration> typeParams = null;
        SourceElement dummy = null;
        TypeReference tr = accept(ctx.typeTypeOrVoid());
        if (ctx.LBRACK().size() != 0) {
            tr.setDimensions(ctx.LBRACK().size());
        }
        if (ctx.THROWS() != null) {
            Throws th = factory.createThrows();
            ASTList<UncollatedReferenceQualifier> nl = accept(ctx.qualifiedNameList());
            ASTList<TypeReference> trl = new ASTArrayList<>();
            for (int i = 0, s = nl.size(); i < s; i++) {
                trl.add(nl.get(i).toTypeReference());
            }
            th.setExceptions(trl);
            result.setThrown(th);
        }
        result.setIdentifier(expect(ctx.identifier()));
        result.setTypeParameters(typeParams);
        body = accept(ctx.methodBody());
        result.setBody(body);
        finish(result, ctx);
        return result;
    }

    @Override
    public ASTList<UncollatedReferenceQualifier> visitQualifiedNameList(JavaKParser.QualifiedNameListContext ctx) {
        return mapOf(ctx.qualifiedName());
    }

    @Override
    public Object visitGenericMethodDeclaration(JavaKParser.GenericMethodDeclarationContext ctx) {
        MethodDeclaration result = expect(ctx.methodDeclaration());
        ASTList<TypeParameterDeclaration> typeParams = accept(ctx.typeParameters());
        result.setTypeParameters(typeParams);
        finish(result, ctx);
        return result;
    }

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

        tr = accept(ctx.typeType());
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


    @Override
    public TypeReference visitTypeTypeOrVoid(JavaKParser.TypeTypeOrVoidContext ctx) {
        if (ctx.VOID() != null) {
            Identifier id = factory.createIdentifier(ctx.VOID().getText());
            TypeReference result = factory.createTypeReference(id);
            finish(id, ctx);
            finish(result, ctx);
            return result;
        }
        return expect(ctx.typeType());
    }

    @Override
    public Object visitTypeType(JavaKParser.TypeTypeContext ctx) {
        TypeReference result = oneOf(ctx.classOrInterfaceType(), ctx.primitiveType());
        int dimension = ctx.LBRACK().size();
        result.setDimensions(dimension);
        finish(result, ctx);
        return result;
    }


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
        return mapOf(ctx.typeArgument());
    }

    @Override
    public TypeArgumentDeclaration visitTypeArgument(JavaKParser.TypeArgumentContext ctx) {
        if (ctx.QUESTION() != null) {
            TypeArgument.WildcardMode wm = TypeArgument.WildcardMode.None;
            TypeArgumentDeclaration result = new TypeArgumentDeclaration();
            TypeReference t = accept(ctx.typeType());
            finish(result, ctx);
            return result;
        } else {//wildcard mode
            TypeArgumentDeclaration result = new TypeArgumentDeclaration();
            //ASTList<DeclarationSpecifier> annot = mapOf(ctx.annotation()); java9
            TypeArgument.WildcardMode wm = TypeArgument.WildcardMode.Any;
            if (ctx.EXTENDS() != null)
                wm = TypeArgument.WildcardMode.Extends;
            else
                wm = TypeArgument.WildcardMode.Super;
            TypeReference t = expect(ctx.typeType());
            result.setTypeReference(t);
            finish(result, ctx);
            result.setWildcardMode(wm);
            return result;
        }
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

    public Assignment visitAssignmentOperator(String op) {
        Assignment result;
        switch (op) {
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
                throw new IllegalStateException("Unexpected value: " + op);
        }
        return result;
    }

    @Override
    public Expression visitConditionalExpression(JavaKParser.ConditionalExpressionContext ctx) {
        Expression cond = accept(ctx.expression(0));
        Expression e1 = accept(ctx.expression(1));
        Expression e2 = accept(ctx.expression(2));
        Operator op = factory.createConditional(cond, e1, e2);
        finish(op, ctx);
        return op;
    }

    @Override
    public Expression visitConditionalOrExpression(JavaKParser.ConditionalOrExpressionContext ctx) {
        Expression result = accept(ctx.expression(0));
        if (ctx.expression().size() == 1) return result;
        Expression expr = accept(ctx.expression(1));
        Operator op = factory.createLogicalOr(result, expr);
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitConditionalAndExpression(JavaKParser.ConditionalAndExpressionContext ctx) {
        Expression result = accept(ctx.expression(0));
        if (ctx.expression().size() == 1) return result;
        Expression expr = accept(ctx.expression(1));
        Operator op = factory.createLogicalAnd(result, expr);
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitInclusiveOrExpression(JavaKParser.InclusiveOrExpressionContext ctx) {
        Expression result = accept(ctx.expression(0));
        if (ctx.expression().size() == 1) return result;
        Expression expr = accept(ctx.expression(1));
        Operator op = factory.createBinaryOr(result, expr);
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitExclusvieOrExpression(JavaKParser.ExclusvieOrExpressionContext ctx) {
        Expression result = accept(ctx.expression(0));
        if (ctx.expression().size() == 1) return result;
        Expression expr = accept(ctx.expression(1));
        Operator op = factory.createBinaryXOr(result, expr);
        finish(result, ctx);
        return result;

    }

    @Override
    public Expression visitAndExpression(JavaKParser.AndExpressionContext ctx) {
        Expression result = accept(ctx.expression(0));
        if (ctx.expression().size() == 1) return result;
        Expression expr = accept(ctx.expression(1));
        Operator op = factory.createBinaryAnd(result, expr);
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitEqualityExpression(JavaKParser.EqualityExpressionContext ctx) {
        Expression result = accept(ctx.expression(0));
        if (ctx.expression().size() == 1) return result;
        Expression expr = accept(ctx.expression(1));
        if (ctx.bop.equals("==")) {
            result = factory.createEquals(result, expr);
        } else {
            result = factory.createNotEquals(result, expr);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitInstanceOfExpression(JavaKParser.InstanceOfExpressionContext ctx) {
        TypeReference tr = expect(ctx.typeType());
        Expression e = expect(ctx.expression());
        Instanceof result = factory.createInstanceof(e, tr);
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitRelationalExpression(JavaKParser.RelationalExpressionContext ctx) {
        Expression result = accept(ctx.expression(0));
        if (ctx.expression().size() == 1) return result;
        Expression expr = accept(ctx.expression(1));
        switch (ctx.bop.getText()) {
            case "<":
                result = factory.createLessThan(result, expr);
                break;
            case ">":
                result = factory.createGreaterThan(result, expr);
                break;
            case "<=":
                result = factory.createLessOrEquals(result, expr);
                break;
            case ">=":
                result = factory.createGreaterOrEquals(result, expr);
                break;
            default:
                assert false;
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitShiftExpression(JavaKParser.ShiftExpressionContext ctx) {
        Expression result = accept(ctx.expression(0));
        Expression expr = accept(ctx.expression(1));
        if (ctx.bop.getText().equals("<<")) {
            result = factory.createShiftRight(result, expr);
        } else if (ctx.bop.getText().equals(">>>")) {
            result = factory.createUnsignedShiftRight(result, expr);
        } else {
            result = factory.createShiftLeft(result, expr);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitAdditiveExpression(JavaKParser.AdditiveExpressionContext ctx) {
        Expression result = accept(ctx.expression(0));
        Expression expr = accept(ctx.expression(1));
        if (ctx.bop.getText().equals("+")) {
            result = factory.createPlus(result, expr);
        } else {
            result = factory.createMinus(result, expr);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitMultiplicativeExpression(JavaKParser.MultiplicativeExpressionContext ctx) {
        Expression result = accept(ctx.expression(0));
        Expression expr = accept(ctx.expression(1));
        if (ctx.bop.getText().equals("*")) {
            result = factory.createTimes(result, expr);
        } else if (ctx.bop.getText().equals("%")) {
            result = factory.createModulo(result, expr);
        } else {
            result = factory.createDivide(result, expr);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitUnaryExpression(JavaKParser.UnaryExpressionContext ctx) {
        Expression result = expect(ctx.expression());
        if (ctx.prefix.getText().equals("~")) {
            result = factory.createBinaryNot(result);
        } else {
            result = factory.createLogicalNot(result);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitPrefixExpression(JavaKParser.PrefixExpressionContext ctx) {
        Expression result = expect(ctx.expression());
        switch (ctx.prefix.getText()) {

            case "++":
                result = factory.createPreIncrement(result);
                break;
            case "--":
                result = factory.createPreDecrement(result);
                break;
            case "+":
                result = result;
                break;
            case "-":
                result = factory.createNegative(result);
                break;
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Expression visitPostfixExpression(JavaKParser.PostfixExpressionContext ctx) {
        Expression result = expect(ctx.expression());
        switch (ctx.postfix.getText()) {
            case "++":
                result = factory.createPostIncrement(result);
                break;
            case "--":
                result = factory.createPostDecrement(result);
                break;
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public TypeCast visitCastExpression(JavaKParser.CastExpressionContext ctx) {
        TypeReference tr = expect(ctx.typeType());
        Expression expr = expect(ctx.expression());
        TypeCast result = factory.createTypeCast(expr, tr);
        finish(result, ctx);
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
    /* TODO try to handle via generic java thingies.
    @Override
    public Expression visitGeneralEscapeExpression(JavaKParser.GeneralEscapeExpressionContext ctx) {
        TerminalNode t = ctx.DL_EMBEDDED_FUNCTION() != null ? ctx.DL_EMBEDDED_FUNCTION() : ctx.MAP_FUNCTION();
        List<Expression> arguments = mapOf(ctx.expression());
        EscapeExpression result = EscapeExpression.getEscapeExpression(t.getText(), arguments);
        finish(result, ctx);
        return result;
    }
    */

    @Override
    public Expression visitAccessExpr(JavaKParser.AccessExprContext ctx) {
        Expression expr = expect(ctx.expression());
        if (ctx.identifier() != null) {
            Identifier id = expect(ctx.identifier());
            expr = factory.createUncollatedReferenceQualifier(
                    (ReferencePrefix) expr, id);
        } else if (ctx.THIS() != null) {
            UncollatedReferenceQualifier o = (UncollatedReferenceQualifier) expr;
            TypeReference tr = o.toTypeReference();
            expr = factory.createThisReference(tr);
        } else if (ctx.SUPER() != null) {
            UncollatedReferenceQualifier o = (UncollatedReferenceQualifier) expr;
            TypeReference tr = o.toTypeReference();
            expr = factory.createSuperReference(tr);
        } else if (ctx.NEW() != null) {
            //nonWildcardTypeArguments? innerCreator
            suffix.type = PrimarySuffixReturnValue.ALLOCATION_EXPR;
            suffix.expr = expr;
            suffix.typeArgs = accept(ctx.nonWildcardTypeArguments());
            //suffix.id = ShortName();
        } else if (ctx.methodCall() != null) {
            MethodReference obj = expect(ctx.methodCall());
            obj.setReferencePrefix((ReferencePrefix) expr);
            expr = obj;
        }
        /* expr=IndexRange()
        {
        // can be simple array access, or subsequence construction
        suffix.type=PrimarySuffixReturnValue.INDEX_EXPR;
        suffix.expr=expr;
        }*/
        finish(expr, ctx);
        return expr;
    }

    @Override
    public Expression visitPrimary(JavaKParser.PrimaryContext ctx) {
        Expression result = null;
        if (ctx.expression() != null) {
            result = accept(ctx.expression());
            result = factory.createParenthesizedExpression(result);
        } else if (ctx.THIS() != null) {
            result = factory.createThisReference();
        } else if (ctx.SUPER() != null) {
            result = factory.createSuperReference();
        } else if (ctx.CLASS() != null) {
            TypeReference tr = expect(ctx.typeTypeOrVoid());
            result = factory.createMetaClassReference(tr);
        } else if (ctx.nonWildcardTypeArguments() != null) {
            assert false;
            //TODO     | nonWildcardTypeArguments (explicitGenericInvocationSuffix | THIS arguments)
        } else if (ctx.identifier() != null) {
            Identifier id = expect(ctx.identifier());
            result = factory.createUncollatedReferenceQualifier(id);
        } else {
            result = expect(ctx.literal());
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Literal visitIntegerLiteral(JavaKParser.IntegerLiteralContext ctx) {
        String text = ctx.getText();
        Literal result;
        if (text.endsWith("L") || text.endsWith("l")) {
            result = factory.createLongLiteral(text);
        } else {
            result = factory.createIntLiteral(text);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Literal visitFloatLiteral(JavaKParser.FloatLiteralContext ctx) {
        String text = ctx.getText();
        Literal result;
        if (text.endsWith("F") || text.endsWith("f")) {
            result = factory.createFloatLiteral(text);
        } else {
            result = factory.createDoubleLiteral(text);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public Literal visitLiteral(JavaKParser.LiteralContext ctx) {
        String text = ctx.getText();
        Literal result = null;
        if (ctx.CHAR_LITERAL() != null) {
            result = factory.createCharLiteral(text);
        } else if (ctx.STRING_LITERAL() != null)
            result = factory.createStringLiteral(text);
        else if (ctx.BOOL_LITERAL() != null) {
            result = factory.createBooleanLiteral(Boolean.parseBoolean(text));
        } else if (ctx.NULL_LITERAL() != null) {
            result = factory.createNullLiteral();
        } else if (ctx.EMPTYSETLITERAL() != null) {
            result = EmptySetLiteral.INSTANCE;
        } else if (ctx.EMPTYSEQLITERAL() != null) {
            result = EmptySeqLiteral.INSTANCE;
        } else if (ctx.EMPTYMAPLITERAL() != null) {
            result = EmptyMapLiteral.INSTANCE;
        } else {
            return oneOf(ctx.integerLiteral(), ctx.floatLiteral());
        }
        assert result != null;
        finish(result, ctx);
        return result;
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
        TypeReference bodySource = accept(ctx.typeType());
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
        Identifier methodName = expect(ctx.identifier());
        ASTList<TypeReference> paramTypes = expect(ctx.formalParameters());
        MethodSignature methodSignature = new MethodSignature(methodName, paramTypes);
        TypeReference classContext = accept(ctx.typeType());
        Expression runtimeInstance = accept(ctx.expression());
        return new ExecutionContext(classContext, methodSignature,
                (ReferencePrefix) runtimeInstance);
    }

    @Override
    public StatementBlock visitBlock(JavaKParser.BlockContext ctx) {
        ASTList<Statement> statements = mapOf(ctx.blockStatement());
        StatementBlock result = factory.createStatementBlock(statements);
        finish(result, ctx);
        return result;
    }

    @Override
    public Statement visitLocalTypeDeclaration(JavaKParser.LocalTypeDeclarationContext ctx) {
        ASTList<DeclarationSpecifier> modifiers = mapOf(ctx.classOrInterfaceModifier());
        if (ctx.classDeclaration() != null) {
            ClassDeclaration td = expect(ctx.classDeclaration());
            td.setDeclarationSpecifiers(modifiers);
            return td;
        } else {
            //InterfaceDeclaration is not a statement!
            InterfaceDeclaration td = expect(ctx.interfaceDeclaration());
            td.setDeclarationSpecifiers(modifiers);
            assert false;
            return null;
        }
    }

    @Override
    public LocalVariableDeclaration visitLocalVariableDeclaration(JavaKParser.LocalVariableDeclarationContext ctx) {
        ASTList<VariableSpecification> vl = expect(ctx.variableDeclarators());
        ASTList<DeclarationSpecifier> declSpecs = mapOf(ctx.variableModifier());
        LocalVariableDeclaration result = factory.createLocalVariableDeclaration();
        if (declSpecs.size() != 0)
            result.setDeclarationSpecifiers(declSpecs);
        TypeReference tr = expect(ctx.typeType());
        result.setTypeReference(tr);
        result.setVariableSpecifications(vl);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitVariableDeclarators(JavaKParser.VariableDeclaratorsContext ctx) {
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
        //| SWITCH parExpression '{' switchBlockStatementGroup* switchLabel* '}' #switchStatement
        List<Branch> b =
                ctx.switchBlockStatementGroup().stream()
                        .flatMap(it -> visitSwitchBlockStatementGroup(it).stream())
                        .collect(Collectors.toList());
        ASTList<Branch> branches = new ASTArrayList<>(b);
        ASTList<Branch> nonBodyCases = mapOf(ctx.switchLabel());
        Switch result = factory.createSwitch();
        Expression expr = accept(ctx.parExpression());
        result.setExpression(expr);
        if (nonBodyCases != null) {
            branches.addAll(nonBodyCases);
        }
        result.setBranchList(branches);
        finish(result, ctx);
        return result;
    }

    @Override
    public ASTList<Branch> visitSwitchBlockStatementGroup(JavaKParser.SwitchBlockStatementGroupContext ctx) {
        ASTList<Branch> branches = mapOf(ctx.switchLabel());
        ASTList<Statement> block = mapOf(ctx.blockStatement());
        Branch result = branches.get(branches.size() - 1);
        if (result instanceof Case) {
            ((Case) result).setBody(block);
        } else {
            ((Default) result).setBody(block);
        }
        finish(result, ctx);
        return branches;
    }

    @Override
    public Branch visitSwitchLabel(JavaKParser.SwitchLabelContext ctx) {
        // handle ctx.enumConstantName()
        if (ctx.CASE() != null) {
            Case result = factory.createCase();
            Expression expr = expect(ctx.expression());
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
    public Object visitIfStatement(JavaKParser.IfStatementContext ctx) {
        If result = factory.createIf();
        Expression cond = accept(ctx.parExpression());
        Then thenStat = factory.createThen();
        Statement trueStat = expect(ctx.then);
        thenStat.setBody(trueStat);
        result.setThen(thenStat);
        if (ctx.ELSE() != null) {
            Else elseStat = factory.createElse();
            Statement falseStat = accept(ctx.otherwise);
            elseStat.setBody(falseStat);
            result.setElse(elseStat);
        }
        result.setExpression(cond);
        finish(result, ctx);
        return result;
    }

    @Override
    public While visitWhileStatement(JavaKParser.WhileStatementContext ctx) {
        Expression expr = accept(ctx.parExpression());
        Statement stat = accept(ctx.statement());
        While result = factory.createWhile();
        result.setGuard(expr);
        result.setBody(stat);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitDoWhileStatement(JavaKParser.DoWhileStatementContext ctx) {
        Do result = factory.createDo();
        Expression expr = accept(ctx.parExpression());
        Statement stat = accept(ctx.statement());
        result.setGuard(expr);
        result.setBody(stat);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitForStatement(JavaKParser.ForStatementContext ctx) {
        LoopStatement loop = expect(ctx.forControl());
        Statement s = expect(ctx.statement());
        loop.setBody(s);
        finish(loop, ctx);
        return loop;
    }

    @Override
    public Object visitForControl(JavaKParser.ForControlContext ctx) {
        if (ctx.SEMI() != null) {
            LoopStatement result;
            ASTList<LoopInitializer> init = accept(ctx.forInit());
            Expression guard = null;
            ASTList<Expression> update = null;
            result = factory.createFor();
            guard = accept(ctx.expression());
            update = accept(ctx.forUpdate);
            result.setInitializers(init);
            result.setGuard(guard);
            result.setUpdates(update);
            finish(result, ctx);
            return result;
        }
        return expect(ctx.enhancedForControl());
    }

    @Override
    public EnhancedFor visitEnhancedForControl(JavaKParser.EnhancedForControlContext ctx) {
        EnhancedFor result = factory.createEnhancedFor();
        @NotNull ASTList<LoopInitializer> init = expect(ctx.variableDeclaratorId());
        @NotNull Expression guard = expect(ctx.expression());
        result.setInitializers(init);
        result.setGuard(guard);
        finish(result, ctx);
        return result;
    }

    @Override
    public ASTList<LoopInitializer> visitForInit(JavaKParser.ForInitContext ctx) {
        ASTList<LoopInitializer> result = new ASTArrayList<>();
        ASTList<Expression> exprs = accept(ctx.expressionList());
        if (exprs != null) {
            for (Expression expr : exprs) {
                result.add((LoopInitializer) expr);
            }
        } else {
            LocalVariableDeclaration varDecl = accept(ctx.localVariableDeclaration());
            result.add(varDecl);
        }
        return result;
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
        expr = accept(ctx.parExpression());
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
        //    | TRY block (catchClause+ finallyBlock? | finallyBlock)   #tryStatement
        Try result = factory.createTry();
        StatementBlock block = expect(ctx.block());
        result.setBody(block);
        ASTList<Branch> catches = mapOf(ctx.catchClause());
        Finally fin = accept(ctx.finallyBlock());
        if (fin != null) catches.add(fin);
        result.setBranchList(catches);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitFinallyBlock(JavaKParser.FinallyBlockContext ctx) {
        Finally result = factory.createFinally();
        Statement block = accept(ctx.block());
        result.setBody(block);
        finish(result, ctx);
        return result;
    }

    @Override
    public Catch visitCatchClause(JavaKParser.CatchClauseContext ctx) {
        //    : CATCH '(' variableModifier* catchType identifier ')' block
        Catch cat = factory.createCatch();
        ASTList<DeclarationSpecifier> modifiers = mapOf(ctx.variableModifier());
        TypeReference tr = expect(ctx.catchType());
        Identifier var = accept(ctx.identifier());
        Statement block = expect(ctx.block());
        cat.setParameterDeclaration(new ParameterDeclaration(modifiers, tr, var));
        cat.setBody(block);
        finish(cat, ctx);
        return cat;
    }

    @Override
    public TypeReference visitCatchType(JavaKParser.CatchTypeContext ctx) {
        if (ctx.qualifiedName().size() > 1) throw new IllegalArgumentException();
        UncollatedReferenceQualifier id = expect(ctx.qualifiedName(0));
        return id.toTypeReference();
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
        return oneOf(ctx.annotation(), ctx.expression(), ctx.elementValueArrayInitializer());
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


    @Override
    public TypeReference visitClassOrInterfaceType(JavaKParser.ClassOrInterfaceTypeContext ctx) {
        ASTList<Identifier> identifiers = mapOf(ctx.identifier());
        UncollatedReferenceQualifier result = null;
        for (Identifier identifier : identifiers) {
            if (result == null) {
                result = factory.createUncollatedReferenceQualifier(identifier);
            } else {
                result = factory.createUncollatedReferenceQualifier(result, identifier);
            }
        }
        //TODO ctx.typeArgumentsOrDiamond()
        finish(result, ctx);
        return result.toTypeReference();
    }

    @Override
    public TypeReference visitCreatedName(JavaKParser.CreatedNameContext ctx) {
        if (null != ctx.primitiveType()) {
            return accept(ctx.primitiveType());
        }
        ASTList<Identifier> identifiers = mapOf(ctx.identifier());
        UncollatedReferenceQualifier result = null;
        for (Identifier identifier : identifiers) {
            if (result == null) {
                result = factory.createUncollatedReferenceQualifier(identifier);
            } else {
                result = factory.createUncollatedReferenceQualifier(result, identifier);
            }
        }
        //TODO ctx.typeArgumentsOrDiamond()
        finish(result, ctx);
        return result.toTypeReference();
    }

    @Override
    public Expression visitInstantiation(JavaKParser.InstantiationContext ctx) {
        Expression result = null;
        boolean classCreator = ctx.creator().classCreatorRest() != null;
        boolean arrayCreator = ctx.creator().arrayCreatorRest() != null;
        if (classCreator) {
            ReferencePrefix accessPath = null; //TODO
            TypeReference constructorName = accept(ctx.creator().createdName());
            @Nullable ASTList<Expression> arguments = accept(ctx.creator().classCreatorRest().arguments());
            @Nullable ClassDeclaration anonymousClass = null;
            ASTList<MemberDeclaration> block = accept(ctx.creator().classCreatorRest().classBody());
            if (block != null) {
                anonymousClass = factory.createClassDeclaration();
                anonymousClass.setMembers(block);
            }
            result = factory.createNew(accessPath, constructorName, arguments, anonymousClass);
        }
        if (arrayCreator) {
            ReferencePrefix accessPath;
            TypeReference arrayName = accept(ctx.creator().createdName());
            ASTList<Expression> dimExpr = mapOf(ctx.creator().arrayCreatorRest().expression());
            ArrayInitializer init = accept(ctx.creator().arrayCreatorRest().arrayInitializer());
            int dims = 0;//TODO
            if (init != null)
                result = factory.createNewArray(arrayName, dims, init);
            else
                result = factory.createNewArray(arrayName, dimExpr);
        }
        finish(result, ctx);
        return result;
    }

    @Override
    protected Object aggregateResult(Object aggregate, Object nextResult) {
        if (aggregate == null && nextResult != null) return nextResult;
        return aggregate;
    }

    @Override
    public Expression visitArrayAccess(JavaKParser.ArrayAccessContext ctx) {
        Expression e = expect(ctx.expression(0));
        Expression idx = expect(ctx.expression(1));
        Expression result = null;
        //weigl: this could maybe replaced with a cast to ReferencePrefix
        if (e instanceof UncollatedReferenceQualifier ||
                e instanceof MethodReference ||
                e instanceof ParenthesizedExpression ||
                //tmpResult instanceof ThisReference || // this[i] in array initialization
                e instanceof ADTPrefixConstruct ||
                e instanceof NewArray ||
                e instanceof VariableReference) {
            if (idx instanceof RangeExpression) {
                result = new SeqSub((ADTPrefixConstruct) e, (RangeExpression) idx);
            } else {
                // Now we know that this is an array reference
                ASTList<Expression> indicees = new ASTArrayList<Expression>(1);
                indicees.add(idx);
                result = factory.createArrayReference((ReferencePrefix) e, indicees);
            }
        } else if (e instanceof ArrayReference) {
            ((ArrayReference) e).getDimensionExpressions().add(idx);
        } else {
            throw new RuntimeException(
                    format("Bad index context - %s in %s", e.getClass().getName(), ctx.getText()));
              /*
                e.g. StringLiteral, TypeReference, NewArray
                (would have to be in parentheses), SuperReference, ...
              */
        }

        finish(result, ctx);
        return result;
    }

    @Override
    public ASTList<Expression> visitExpressionList(JavaKParser.ExpressionListContext ctx) {
        return mapOf(ctx.expression());
    }

    @Override
    public JavaNonTerminalProgramElement visitMethodCall(JavaKParser.MethodCallContext ctx) {
        ASTList<Expression> args = accept(ctx.expressionList());
        JavaNonTerminalProgramElement result = null;
        if (ctx.identifier() != null) {
            Identifier name = accept(ctx.identifier());
            result = factory.createMethodReference(name, args);
        }

        if (ctx.THIS() != null) {
            result = factory.createThisConstructorReference(args);
        }

        if (ctx.SUPER() != null) {
            result = factory.createSuperConstructorReference(args);
        }

        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitMethodCallExpr(JavaKParser.MethodCallExprContext ctx) {
        return expect(ctx.methodCall());
    }

    @Override
    public Statement visitStatementExpression(JavaKParser.StatementExpressionContext ctx) {
        @NotNull Object e = expect(ctx.expression());
        try {
            return (Statement) e;
        } catch (ClassCastException aaa) {
            Expression a = expect(ctx.expression());
            return null;
        }
    }

    @Override
    public Object visitAssignExpression(JavaKParser.AssignExpressionContext ctx) {
        Assignment result = null;
        Expression lhs = expect(ctx.expression(0));
        Expression rhs = expect(ctx.expression(1));
        switch (ctx.bop.getText()) {
            case "=":
                result = factory.createCopyAssignment(lhs, rhs);
                break;
            case "+=":
                result = factory.createPlusAssignment(lhs, rhs);
                break;
            case "*=":
                result = factory.createTimesAssignment(lhs, rhs);
                break;
            case "-=":
                result = factory.createMinusAssignment(lhs, rhs);
                break;
            case "/=":
                result = factory.createDivideAssignment(lhs, rhs);
                break;
            case "&=":
                result = factory.createBinaryAndAssignment(lhs, rhs);
                break;
            case "|=":
                result = factory.createBinaryOrAssignment(lhs, rhs);
                break;
            case "^=":
                result = factory.createBinaryXOrAssignment(lhs, rhs);
                break;
            case ">>=":
                result = factory.createShiftRightAssignment(lhs, rhs);
                break;
            case ">>>=":
                result = factory.createUnsignedShiftRightAssignment(lhs, rhs);
                break;
            case "<<=":
                result = factory.createShiftLeftAssignment(lhs, rhs);
                break;
            case "%=":
                result = factory.createModuloAssignment(lhs, rhs);
                break;
            default:
                assert false;
        }
        finish(result, ctx);
        return result;
    }

    @Override
    public ASTList<ParameterDeclaration>  visitFormalParameters(JavaKParser.FormalParametersContext ctx) {
        return accept(ctx.formalParameterList());
    }

    @Override
    public ASTList<ParameterDeclaration>  visitFormalParameterList(JavaKParser.FormalParameterListContext ctx) {
        ASTList<ParameterDeclaration> seq =  mapOf(ctx.formalParameter());
        if (ctx.lastFormalParameter() != null) {
            seq.add(expect(ctx.lastFormalParameter()));
        }
        return seq;
    }

    @Override
    public ConstructorDeclaration visitConstructorDeclaration(JavaKParser.ConstructorDeclarationContext ctx) {
        ConstructorDeclaration result = factory.createConstructorDeclaration();
        Identifier id = expect(ctx.identifier());
        @Nullable ASTList<ParameterDeclaration> pdl = accept(ctx.formalParameters());
        if (ctx.THROWS() != null) {
            Throws th = factory.createThrows();
            result.setThrown(th);
        }
        result.setBody(expect(ctx.block()));
        result.setIdentifier(id);
        result.setParameters(pdl);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitGenericConstructorDeclaration(JavaKParser.GenericConstructorDeclarationContext ctx) {
        ConstructorDeclaration result = expect(ctx.constructorDeclaration());
        ASTList<TypeParameterDeclaration> typeParams = expect(ctx.typeParameters());
        result.setTypeParameters(typeParams);
        finish(result, ctx);
        return result;
    }

    @Override
    public Object visitGenericInterfaceMethodDeclaration(JavaKParser.GenericInterfaceMethodDeclarationContext ctx) {
        return super.visitGenericInterfaceMethodDeclaration(ctx);
    }

    @Override
    public Object visitLambdaExpression(JavaKParser.LambdaExpressionContext ctx) {
        throw new RuntimeException();
    }

    @Override
    public Object visitLambdaParameters(JavaKParser.LambdaParametersContext ctx) {
        throw new RuntimeException();
    }

    @Override
    public Object visitLambdaBody(JavaKParser.LambdaBodyContext ctx) {
        throw new RuntimeException();
    }
}