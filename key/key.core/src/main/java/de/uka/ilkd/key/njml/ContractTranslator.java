package de.uka.ilkd.key.njml;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.ClassInvariantImpl;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLTranslationExceptionManager;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (5/12/20)
 */
@SuppressWarnings("all")
public class ContractTranslator extends JmlParserBaseVisitor<Object> {
    private SLTranslationExceptionManager excManager;
    private ImmutableSet<PositionedString> warnings = DefaultImmutableSet.<PositionedString>nil();
    private ImmutableSLList<String> mods;
    final JMLSpecFactory2 factory;
    private final KeYJavaType kjt;
    private Object currentBehavior;

    private ContractTranslator(String fileName, Position offsetPos, JMLSpecFactory2 factory, KeYJavaType kjt) throws SLTranslationException {
        this.factory = factory;
        this.kjt = kjt;
        this.excManager = new SLTranslationExceptionManager(null, fileName, offsetPos);
    }

    private PositionedString createPositionedString(String text, Token t) {
        return excManager.createPositionedString(text, new Position(t.getLine(), t.getCharPositionInLine()));
    }

    private PositionedString createPositionedString(final String text,
                                                    final Position pos) {
        return excManager.createPositionedString(text, pos);
    }


    private void raiseError(String msg) throws SLTranslationException {
        throw excManager.createException(msg);
    }


    private void raiseNotSupported(String feature) {
        PositionedString warning = excManager.createPositionedString(feature + " not supported");
        warnings = warnings.add(warning);
    }


    public ImmutableSet<PositionedString> getWarnings() {
        return warnings;
    }

    private PositionedString flipHeaps(String declString, PositionedString result) {
        return flipHeaps(declString, result, false);
    }

    /*
     * This method prepends a String to a given PositionedString and removes whitespaces from
     * heap brackets at the beginning of it. (Why is this necessary?)
     *
     * Note: Static manipulation of Strings that are passed to KeYJMLParser is fragile when it
     * comes to error reporting. Original JML input should be left unmodified as much as possible
     * so that correct error location can be reported to the user. Functionality of this method
     * should be replaced by a more accurate implementation. (Kai Wallisch 07/2015)
     */
    private PositionedString flipHeaps(String declString, PositionedString result, boolean allowPreHeaps) {
        String t = result.text;
        String p = declString;

        List<Name> validHeapNames = new ArrayList<Name>();

        for (Name heapName : HeapLDT.VALID_HEAP_NAMES) {
            validHeapNames.add(heapName);
            if (allowPreHeaps) {
                validHeapNames.add(new Name(heapName.toString() + "AtPre"));
            }
        }
        for (Name heapName : validHeapNames) {
            t = t.trim();
            String l = "<" + heapName + ">";
            String lsp = "< " + heapName + " >";
            if (t.startsWith(l) || t.startsWith(lsp)) {
                p = l + p;
                t = t.substring(t.startsWith(lsp) ? lsp.length() : l.length());
                result = new PositionedString(t, result.fileName, result.pos);
            }
        }
        if (p.contains("<")) {
            /*
             * Using normal prepend without update of position in case p contains a heap
             * because in that case prependAndUpdatePosition() might produce a negative
             * column value. However, this alternative is also not ideal because it does
             * not update the position after prepending a string. A rewrite of this
             * method that does not rely on low-level string manipulation is recommended
             * to fix this issue.
             */
            result = result.prepend(p + " ");
        } else {
            result = result.prependAndUpdatePosition(p + " ");
        }
        return result;
    }


    private <T> @Nullable T accept(@Nullable ParserRuleContext ctx) {
        return (T) ctx.accept(this);
    }

    private <T> List<T> mapOf(List<? extends ParserRuleContext> contexts) {
        return contexts.stream().map(it -> (T) accept(it)).collect(Collectors.toList());
    }

    private <T> ImmutableList<T> listOf(List<? extends ParserRuleContext> contexts) {
        ImmutableList<T> seq = ImmutableSLList.nil();
        for (ParserRuleContext context : contexts) {
            seq = seq.append((T) accept(context));
        }
        return seq;
    }


    @Override
    public ImmutableList<TextualJMLConstruct> visitClasslevel_comment(JmlParser.Classlevel_commentContext ctx) {
        ImmutableList<TextualJMLConstruct> result = ImmutableSLList.<TextualJMLConstruct>nil();
        this.mods = ImmutableSLList.<String>nil();
        /* there may be some modifiers after the declarations */
        this.mods = listOf(ctx.modifiers());
        result = listOf(ctx.classlevel_element());
        ImmutableSLList<String> mods = modifiers;
        this.mods = (ImmutableSLList<String>) mods.prepend(this.mods);
        return result;
    }

    @Override
    public ImmutableList<TextualJMLConstruct> visitMethodlevel_comment(JmlParser.Methodlevel_commentContext ctx) {
        ImmutableList<TextualJMLConstruct> result = ImmutableSLList.<TextualJMLConstruct>nil();
        mods = ImmutableSLList.<String>nil();
        return listOf(ctx.methodlevel_element());
    }

    @Override
    public ImmutableList<String> visitModifiers(JmlParser.ModifiersContext ctx) {
        return listOf(ctx.modifier());
    }

    @Override
    public String visitModifier(JmlParser.ModifierContext ctx) {
        return ctx.getText();
    }


    @Override
    public ClassInvariantImpl visitClass_invariant(JmlParser.Class_invariantContext ctx) {
        ImmutableList<TextualJMLConstruct> result;
        String name = null;
        ctx.expression().getText();
        Term expr = accept(ctx.expression());
        return factory.createJMLClassInvariant(kjt, mods, name, ctx.expression());
    }

    @Override
    public Object visitClass_axiom(JmlParser.Class_axiomContext ctx) {
        // axiom statements may not be prefixed with any modifiers (see Sect. 8 of the JML reference manual)
        if (!mods.isEmpty())
            raiseNotSupported("modifiers in axiom clause");
        return factory.createJMLClassAxiom(kjt, mods, ctx.expression());
    }

    @Override
    public Object visitInitially_clause(JmlParser.Initially_clauseContext ctx) {
        for (String s : mods) {
            if (!(s.equals("public") || s.equals("private") || s.equals("protected")))
                raiseNotSupported("modifier " + s + " in initially clause");
        }
        return factory.createJMLInitiallyClause(kjt, mods, ctx.expression());
    }


    @Override
    public Object visitMethod_specification(JmlParser.Method_specificationContext ctx) {
        return listOf(ctx.spec_case());
    }


    @Override
    public Object visitLightweight_spec_case(JmlParser.Lightweight_spec_caseContext ctx) {
        currentBehavior = Behavior.NONE;
        return accept(ctx.generic_spec_case());
    }

    private <T> @Nullable T oneOf(ParserRuleContext @Nullable ... contexts) {
        for (ParserRuleContext context : contexts) {
            T t = accept(context);
            if (t != null) return t;
        }
        return null;
    }


    @Override
    public Object visitHeavyweight_spec_case(JmlParser.Heavyweight_spec_caseContext ctx) {
        mods = accept(ctx.modifier());
        return oneOf(ctx.behavior_spec_case(), ctx.break_behavior_spec_case(),
                ctx.continue_behavior_spec_case(), ctx.exceptional_behavior_spec_case(), ctx.normal_behavior_spec_case(),
                ctx.model_behavior_spec_case(), ctx.return_behavior_spec_case());
    }


    @Override
    public Object visitBehavior_spec_case(JmlParser.Behavior_spec_caseContext ctx) {
        currentBehavior = Behavior.BEHAVIOR;
        return accept(ctx.generic_spec_case());
    }

    @Override
    public Object visitNormal_behavior_spec_case(JmlParser.Normal_behavior_spec_caseContext ctx) {
        currentBehavior = Behavior.NORMAL_BEHAVIOR;
        return accept(ctx.generic_spec_case());
    }

    @Override
    public Object visitModel_behavior_spec_case(JmlParser.Model_behavior_spec_caseContext ctx) {
        currentBehavior = Behavior.MODEL_BEHAVIOR;
        return accept(ctx.generic_spec_case());
    }

    @Override
    public Object visitExceptional_behavior_spec_case(JmlParser.Exceptional_behavior_spec_caseContext ctx) {
        currentBehavior = Behavior.;
        return accept(ctx.generic_spec_case());
    }


    @Override
    public Object visitGeneric_spec_case(JmlParser.Generic_spec_caseContext ctx) {
        (abbrvs = spec_var_decls) ?
                ((requires = spec_header
                        (requires_free = free_spec_header) ?)
        (

                options {
            greedy = true;
        }
	 :result = generic_spec_body[mods, b, result])?

        {
            if (result.isEmpty()) {
                result = result.append(new TextualJMLSpecCase(mods, b));
            }

            for (Iterator<TextualJMLConstruct> it = result.iterator();
                 it.hasNext(); ) {
                TextualJMLSpecCase sc = (TextualJMLSpecCase) it.next();
                if (requires != null) {
                    sc.addRequires(requires);
                }
                if (requires_free != null) {
                    sc.addRequiresFree(requires_free);
                }
                if (abbrvs != null) {
                    for (PositionedString[] pz : abbrvs) {
                        sc.addAbbreviation(pz);
                    }
                }
            }
        }
    |result = generic_spec_body[mods, b, result]
            );
    }

    @Override
    public ImmutableList<PositionedString> visitSpec_var_decls(JmlParser.Spec_var_declsContext ctx) {
        pz = old_clause {
            result = result.append(pz);
        }
    |FORALL ps = expression {
            raiseNotSupported("specification variables");
        }
    }


    @Override
    public Object visitSpec_header(JmlParser.Spec_headerContext ctx) {
        return listOf(ctx.requires_clause());
    }

    @Override
    public Object visitRequires_clause(JmlParser.Requires_clauseContext ctx) {
        //result = flipHeaps("requires_free", result);
        result = flipHeaps("requires", result);
    }

    generic_spec_body[
    ImmutableList<String> mods
    b,
    ImmutableList<TextualJMLConstruct> specs]
    returns [
    ImmutableList<TextualJMLConstruct> r = null]
            throws SLTranslationException

    @init {
        TextualJMLSpecCase sc;
        result = r;
    }

    @after {
        r = result;
    }
:
    result=simple_spec_body[mods,b]
            |
            (
    NEST_START
    result=generic_spec_case_seq[mods,b,specs]
    NEST_END
    );


    generic_spec_case_seq[
    ImmutableList<String> mods
    ImmutableList<TextualJMLConstruct> specs]
    returns [
    ImmutableList<TextualJMLConstruct> r = ImmutableSLList.nil()]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        for (TextualJMLConstruct tc : result)
            for (TextualJMLConstruct z : specs) {
                TextualJMLSpecCase a = (TextualJMLSpecCase) tc;
                TextualJMLSpecCase c = (TextualJMLSpecCase) z;
                System.out.println("---Contract A:\n" + a);
                System.out.println("---Contract B:\n" + c);
                r.append(a.merge(c));
            }
    }
:
    result=generic_spec_case[mods,b]
            (
            (also_keyword)+
    list=generic_spec_case[mods,b]

    {
        result = result.append(list);
    }
    )*;


    simple_spec_body[
    ImmutableList<String> mods, b]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException

    @init {
        TextualJMLSpecCase sc = new TextualJMLSpecCase(mods, b);
        result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(sc);
    }
:
        (

    options {
        greedy = true;
    }
	:
    simple_spec_body_clause[sc,b]
            )+;


    simple_spec_body_clause[
    TextualJMLSpecCase sc, Behavior
    b]
            throws SLTranslationException

    @init {
        PositionedString[] pss;
    }
:
        (
    ps=

    assignable_clause {
        sc.addAssignable(ps);
    }
	|ps=

    accessible_clause {
        sc.addAccessible(ps);
    }
	|ps=

    ensures_clause {
        sc.addEnsures(ps);
    }
	|ps=

    ensures_free_clause {
        sc.addEnsuresFree(ps);
    }
	|ps=

    signals_clause {
        sc.addSignals(ps);
    }
	|ps=

    signals_only_clause {
        sc.addSignalsOnly(ps);
    }
	|ps=

    diverges_clause {
        sc.addDiverges(ps);
    }
	|ps=

    measured_by_clause {
        sc.addMeasuredBy(ps);
    }
	|ps=

    variant_function {
        sc.addDecreases(ps);
    }
	|ps=

    name_clause {
        sc.addName(ps);
    }
	|captures_clause
	|when_clause
	|working_space_clause
	|duration_clause
	|ps=

    breaks_clause {
        sc.addBreaks(ps);
    }
	|ps=

    continues_clause {
        sc.addContinues(ps);
    }
	|ps=

    returns_clause {
        sc.addReturns(ps);
    }
        |ps=

    separates_clause {
        sc.addInfFlowSpecs(ps);
    }
        |ps=

    determines_clause {
        sc.addInfFlowSpecs(ps);
    }
    )

    {
        if (b == Behavior.EXCEPTIONAL_BEHAVIOR
                && !sc.getEnsures().isEmpty()) {
            raiseError("ensures not allowed in exceptional behavior.");
        } else if (b == Behavior.NORMAL_BEHAVIOR
                && !sc.getSignals().isEmpty()) {
            raiseError("signals not allowed in normal behavior.");
        } else if (b == Behavior.NORMAL_BEHAVIOR
                && !sc.getSignalsOnly().isEmpty()) {
            raiseError("signals_only not allowed in normal behavior.");
        } else if (b == Behavior.NORMAL_BEHAVIOR
                && !sc.getBreaks().isEmpty()) {
            raiseError("breaks not allowed in normal behavior.");
        } else if (b == Behavior.NORMAL_BEHAVIOR
                && !sc.getContinues().isEmpty()) {
            raiseError("continues not allowed in normal behavior.");
        } else if (b == Behavior.NORMAL_BEHAVIOR
                && !sc.getReturns().isEmpty()) {
            raiseError("returns not allowed in normal behavior.");
        }
    }

    ;


//-----------------------------------------------------------------------------
//simple specification body clauses
//-----------------------------------------------------------------------------


    // old information flow annotations
    separates_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    separates_keyword result = expression

    {
        result = result.prepend("separates ");
    }

    ;


    separates_keyword
:
    RESPECTS
    |SEPARATES;


    determines_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    determines_keyword result = expression

    {
        result = result.prepend("determines ");
    }

    ;


    determines_keyword
:
    DETERMINES;


    assignable_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    assignable_keyword result = expression

    {
        result = flipHeaps("assignable", result);
    }

    ;


    assignable_keyword
:
    ASSIGNABLE
    |ASSIGNABLE_RED
    |ASSIGNS
    |ASSIGNS_RED
    |MODIFIABLE
    |MODIFIABLE_RED
    |MODIFIES
    |MODIFIES_RED;


    accessible_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    accessible_keyword result = expression

    {
        result = flipHeaps("accessible", result, true);
    }

    ;


    accessible_keyword
:
    ACCESSIBLE
    |ACCESSIBLE_REDUNDANTLY;


    measured_by_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    // TODO: this is confusing. why not keep 'measured_by'?
    measured_by_keyword result = expression

    {
        result = result.prepend("decreases ");
    }

    ;


    measured_by_keyword
:
    MEASURED_BY
    |MEASURED_BY_REDUNDANTLY;


    ensures_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    ensures_keyword result = expression

    {
        result = flipHeaps("ensures", result);
    }

    ;


    ensures_keyword
:
    ENSURES |ENSURES_RED |POST |POST_RED;


    ensures_free_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    ENSURES_FREE result = expression

    {
        result = flipHeaps("ensures_free", result);
    }

    ;


    signals_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    signals_keyword result = expression

    {
        result = result.prepend("signals ");
    }

    ;


    signals_keyword
:
    SIGNALS
    |SIGNALS_RED
    |EXSURES
    |EXSURES_RED;


    signals_only_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    signals_only_keyword result = expression

    {
        result = result.prepend("signals_only ");
    }

    ;


    signals_only_keyword
:
    SIGNALS_ONLY
    |SIGNALS_ONLY_RED;


    diverges_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    diverges_keyword result = expression;


    diverges_keyword
:
    DIVERGES
    |DIVERGES_RED;


    captures_clause throws SLTranslationException
:
    captures_keyword ps = expression

    {
        raiseNotSupported("captures clauses");
    }

    ;


    captures_keyword
:
    CAPTURES
    |CAPTURES_RED;


    name_clause
            returns[
    PositionedString result = null]
            throws SLTranslationException
:
    spec=
    SPEC_NAME name = STRING_LITERAL

    SEMICOLON {
        result = createPositionedString(name.getText().substring(1, name.getText().length() - 1), spec);
    }

    ;


    when_clause throws SLTranslationException
:
    when_keyword ps = expression

    {
        raiseNotSupported("when clauses");
    }

    ;


    when_keyword
:
    WHEN
    |WHEN_RED;


    working_space_clause throws SLTranslationException
:
    working_space_keyword ps = expression

    {
        raiseNotSupported("working_space clauses");
    }

    ;


    working_space_keyword
:
    WORKING_SPACE
    |WORKING_SPACE_RED;


    duration_clause throws SLTranslationException
:
    duration_keyword ps = expression

    {
        raiseNotSupported("duration clauses");
    }

    ;


    duration_keyword
:
    DURATION
    |DURATION_RED;

    old_clause
    returns [PositionedString[\]result =new PositionedString[3\]]
            throws SLTranslationException
:
    OLD mods = modifiers
    typeps=
    type
            name = IDENT
    init=

    INITIALISER { // modifiers are ignored, don't make any sense here
        result[0] = typeps;
        result[1] = new PositionedString(name.getText(), name);
        result[2] = new PositionedString(init.getText().substring(2), init);
    }

    ;

    type returns[
    PositionedString text = null;]

    @init {
        StringBuffer sb = new StringBuffer();
    }

    @after {
        text = new PositionedString(sb.toString(), identToken);
    }
:
    identToken=

    IDENT {
        sb.append(identToken.getText());
    }
    (t=

    EMPTYBRACKETS {
        sb.append(t.getText());
    })*;

    field_or_method_declaration[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            :
    typeps=
    type name = IDENT
    ((LPAREN)=>methodDecl =method_declaration[mods,typeps,name]

    {
        result = methodDecl;
    }
      |
    fieldDecl =field_declaration[mods,typeps,name]

    {
        result = fieldDecl;
    }
    );


//-----------------------------------------------------------------------------
//field declarations
//-----------------------------------------------------------------------------

    field_declaration[
    ImmutableList<String> mods, PositionedString
    type,
    Token name]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]

    @init {
        StringBuffer sb = new StringBuffer(type.text + " " + name.getText());
        String s;
    }
:
        (t=

    EMPTYBRACKETS {
        sb.append(t.getText());
    })*
            (
    init=

    initialiser {
        sb.append(init);
    }
	|semi=

    SEMICOLON {
        sb.append(semi.getText());
    }
    )

    {
        PositionedString ps = createPositionedString(sb.toString(), type.pos);
        TextualJMLFieldDecl fd = new TextualJMLFieldDecl(mods, ps);
        result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(fd);
    }

    ;


//-----------------------------------------------------------------------------
//method declarations
//-----------------------------------------------------------------------------

    method_declaration[
    ImmutableList<String> mods, PositionedString
    type,
    Token name]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]

    @init {
        StringBuffer sb = new StringBuffer(type.text + " " + name.getText());
        StringBuffer sbDefinition = new StringBuffer();
        String s;
    }
:
    params=

    param_list {
        sb.append(params);
    }
    (
    body=

    BODY {
        sbDefinition.append(body.getText());
    }
	|semi=SEMICOLON
    )

    {
        sb.append(";");
        PositionedString ps = createPositionedString(sb.toString(), type.pos);
        PositionedString psDefinition = null;
        if (sbDefinition.length() > 0) {
            String paramsString = params.trim();
            String bodyString = new String(sbDefinition).trim();
            assert paramsString.charAt(0) == '(' && paramsString.charAt(paramsString.length() - 1) == ')';
            paramsString = paramsString.substring(1, paramsString.length() - 1).trim();
            if (!paramsString.equals("")) {
                StringBuffer stmp = new StringBuffer();
                for (String t : paramsString.split(",")) {
                    t = t.trim();
                    t = t.substring(t.indexOf(" ") + 1);
                    if (stmp.length() > 0) stmp.append(", ");
                    stmp.append(t);
                }
                paramsString = "(" + new String(stmp) + ")";
            } else {
                paramsString = "()";
            }
            assert bodyString.charAt(0) == '{' && bodyString.charAt(bodyString.length() - 1) == '}';
            bodyString = bodyString.substring(1, bodyString.length() - 1).trim();
            assert bodyString.startsWith("return ") : "return expected, instead: " + bodyString;
            int beginIndex = bodyString.indexOf(" ") + 1;
            int endIndex = bodyString.lastIndexOf(";");
            bodyString = bodyString.substring(beginIndex, endIndex);

            // TODO Other heaps? There is only one return statement.....
            // TODO Better not encoded as a string but create equality directly.
            psDefinition = createPositionedString("<heap> " + name.getText() +
                    paramsString + " == (" + bodyString + ");", type.pos);
        }

        TextualJMLMethodDecl md
                = new TextualJMLMethodDecl(mods, ps, name.getText(), psDefinition);
        result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(md);
    }

    ;

    param_list returns[
    String s = null]

    @init {
        final StringBuilder text = new StringBuilder();
    }

    @after {
        s = text.toString();
    }
    :
    t=

    LPAREN {
        text.append(t.getText());
    }
        (
    param=

    param_decl {
        text.append(param);
    }
            (
    t=
    COMMA
            param = param_decl

    {
        text.append(t.getText() + param);
    }
            )*
                    )?
    t=

    RPAREN {
        text.append(t.getText());
    }

    ;

    param_decl returns[
    String s = null]

    @init {
        final StringBuilder text = new StringBuilder();
    }

    @after {
        s = text.toString();
    }
    :
            (
    t=(NON_NULL |NULLABLE)

    {
        text.append("/*@" + t.getText() + "@*/");
    }
        )?
    t=

    IDENT {
        text.append(t.getText());
    }
        (
                (
    AXIOM_NAME_BEGIN // That is "["
            AXION_NAME_END // That is "]"
          |EMPTYBRACKETS )

    {
        text.append("[]");
    }
        )*
    t=

    IDENT {
        text.append(" " + t.getText());
    }

    ;


//-----------------------------------------------------------------------------
//represents clauses
//-----------------------------------------------------------------------------


    represents_clause[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException
:
    represents_keyword ps = expression

    {
        TextualJMLRepresents rc
                = new TextualJMLRepresents(mods, ps.prepend("represents "));
        result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(rc);
    }

    ;


    represents_keyword
:
    REPRESENTS
    |REPRESENTS_RED;


//-----------------------------------------------------------------------------
//classlevel depends clauses (custom extension of JML)
//-----------------------------------------------------------------------------

    depends_clause[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException
:
    accessible_keyword ps = expression

    {
        TextualJMLDepends d
                = new TextualJMLDepends(mods, flipHeaps("depends", ps, false));
        result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(d);
    }

    ;


//-----------------------------------------------------------------------------
//unsupported classlevel stuff
//-----------------------------------------------------------------------------

    history_constraint[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException
:
    constraint_keyword ps = expression

    {
        raiseNotSupported("history constraints");
        result = ImmutableSLList.<TextualJMLConstruct>nil();
    }

    ;


    constraint_keyword
:
    CONSTRAINT
    |CONSTRAINT_RED;


    monitors_for_clause[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException
:
    MONITORS_FOR ps = expression

    {
        raiseNotSupported("monitors_for clauses");
        result = ImmutableSLList.<TextualJMLConstruct>nil();
    }

    ;


    readable_if_clause[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException
:
    READABLE ps = expression

    {
        raiseNotSupported("readable-if clauses");
        result = ImmutableSLList.<TextualJMLConstruct>nil();
    }

    ;


    writable_if_clause[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException
:
    WRITABLE ps = expression

    {
        raiseNotSupported("writable-if clauses");
        result = ImmutableSLList.<TextualJMLConstruct>nil();
    }

    ;


    datagroup_clause[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException
:
    in_group_clause |maps_into_clause;


    in_group_clause  throws SLTranslationException
:
    in_keyword ps = expression

    {
        raiseNotSupported("in-group clauses");
    }

    ;


    in_keyword
:
    IN
    |IN_RED;


    maps_into_clause throws SLTranslationException
:
    maps_keyword ps = expression

    {
        raiseNotSupported("maps-into clauses");
    }

    ;


    maps_keyword
:
    MAPS
    |MAPS_RED;


    nowarn_pragma[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException
:
    NOWARN ps = expression

    {
        raiseNotSupported("nowarn pragmas");
        result = ImmutableSLList.<TextualJMLConstruct>nil();
    }

    ;


    debug_statement[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException
:
    DEBUG ps = expression

    {
        raiseNotSupported("debug statements");
        result = ImmutableSLList.<TextualJMLConstruct>nil();
    }

    ;


//-----------------------------------------------------------------------------
//set statements
//-----------------------------------------------------------------------------

    set_statement[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            :
    SET ps = expression

    {
        TextualJMLSetStatement ss = new TextualJMLSetStatement(mods, ps);
        result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(ss);
    }

    ;

//-----------------------------------------------------------------------------
//merge point statement
//-----------------------------------------------------------------------------

    merge_point_statement[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            :

    MERGE_POINT
            (MERGE_PROC   (mpr=STRING_LITERAL))?
            (

    MERGE_PARAMS(mpa =BODY))?

    SEMICOLON {
        TextualJMLMergePointDecl mpd =
                mpr == null ?
                        new TextualJMLMergePointDecl(mods) :
                        (mpa == null ?
                                new TextualJMLMergePointDecl(mods, createPositionedString(mpr.getText(), mpr)) :
                                new TextualJMLMergePointDecl(mods, createPositionedString(mpr.getText(), mpr), createPositionedString(mpa.getText(), mpa)));
        result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(mpd);
    }

    ;


//-----------------------------------------------------------------------------
//loop specifications
//-----------------------------------------------------------------------------

    loop_specification[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException

    @init {
        TextualJMLLoopSpec ls = new TextualJMLLoopSpec(mods);
        result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(ls);
    }
:
        (ps=

    loop_invariant {
        ls.addInvariant(ps);
    }
    |ps=

    loop_invariant_free {
        ls.addFreeInvariant(ps);
    })
            (

    options {
        greedy = true;
    }
	:
    ps=

    loop_invariant {
        ls.addInvariant(ps);
    }
        |ps=

    loop_invariant_free {
        ls.addFreeInvariant(ps);
    }
        |ps=

    loop_separates_clause {
        ls.addInfFlowSpecs(ps);
    }
        |ps=

    loop_determines_clause {
        ls.addInfFlowSpecs(ps);
    }
        |ps=

    assignable_clause {
        ls.addAssignable(ps);
    }
        |ps=

    variant_function {
        ls.setVariant(ps);
    }
    )*;


    loop_invariant returns[
    PositionedString r = null]

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    maintaining_keyword result = expression

    {
        result = flipHeaps("", result);
    }

    ;
    loop_invariant_free returns[
    PositionedString r = null]

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    LOOP_INVARIANT_FREE result = expression

    {
        result = flipHeaps("", result);
    }

    ;

    maintaining_keyword
:
    MAINTAINING
    |MAINTAINING_REDUNDANTLY
    |LOOP_INVARIANT
    |LOOP_INVARIANT_REDUNDANTLY;


    variant_function returns[
    PositionedString r = null]

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    decreasing_keyword result = expression

    {
        result = result.prepend("decreases ");
    }

    ;


    decreasing_keyword
:
    DECREASING
    |DECREASING_REDUNDANTLY
    |DECREASES
    |DECREASES_REDUNDANTLY
    |LOOP_VARIANT
    |LOOP_VARIANT_RED;


    // old information flow annotations
    loop_separates_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    separates_keyword result = expression

    {
        result = result.prepend("loop_separates ");
    }

    ;


    loop_determines_clause
            returns[
    PositionedString r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:
    determines_keyword result = expression

    {
        result = result.prepend("loop_determines ");
    }

    ;


//-----------------------------------------------------------------------------
//unsupported methodlevel stuff
//-----------------------------------------------------------------------------


    assume_statement[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> result = null]
            throws SLTranslationException
:
    assume_keyword ps = expression

    {
        raiseNotSupported("assume statements");
        result = ImmutableSLList.<TextualJMLConstruct>nil();
    }

    ;


    assume_keyword
:
    ASSUME
    |ASSUME_REDUNDANTLY;


//-----------------------------------------------------------------------------
//expressions
//-----------------------------------------------------------------------------


    expression returns[
    PositionedString result = null]

    @init {
        int parenthesesCounter = 0;
        // final StringBuilder text = new StringBuilder();
        Token begin = null;
    }
:
        (
        (
    t=

    LPAREN {
        parenthesesCounter++;
    }
        |t=

    RPAREN {
        parenthesesCounter--;
    }
        |

    {
        parenthesesCounter > 0
    }?t=SEMICOLON
        |t=~(LPAREN |RPAREN |SEMICOLON)
            )

    {
        if (begin == null) {
            begin = t;
        } /*text.append(" " + t.getText());*/
    }
    )*

    {
        parenthesesCounter == 0
    }?t=

    SEMICOLON {
        if (begin == null) {
            begin = t;
        } /*text.append(t.getText());*/
    }

    {
        // take the string from the token stream
        // (do not reconstruct it with false whitespaces)
        String coveredText = input.toString(begin, input.LT(-1));
        result = createPositionedString(coveredText, begin);
    }

    ;

    initialiser returns[
    String s = null]
            :
    EQUALITY ps = expression

    {
        s = "=" + ps.text;
    }

    ;


//-----------------------------------------------------------------------------
//block specifications
//-----------------------------------------------------------------------------

    block_specification[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> r = null]
            throws SLTranslationException

    @init {
        result = r;
    }

    @after {
        r = result;
    }
:

    result=method_specification[mods];

    block_loop_specification[
    ImmutableList<String> mods]
    returns [
    ImmutableList<TextualJMLConstruct> r = null]
            throws SLTranslationException

    @init {
        list = ImmutableSLList.<TextualJMLConstruct>nil();
        result = r;
    }

    @after {
        r = result;
    }
:
        (
    loop_contract_keyword result = spec_case[mods]
    (

    options {
        greedy = true;
    }
	:
            (also_keyword)+
    loop_contract_keyword list = spec_case[ImmutableSLList.<String>nil()]

    {
        result = result.append(list);
    }
    )*)

    {
        for (TextualJMLConstruct construct : result) {
            construct.setLoopContract(true);
        }
    }

    @Override
    public Object visitAssert_statement(JmlParser.Assert_statementContext ctx) {
        if (ctx.UNREACHABLE() != null) {
            TextualJMLSpecCase.assert2blockContract(mods, new PositionedString("false"));
        } else {
            TextualJMLSpecCase.assert2blockContract(mods, ps);
            Term t = accept(ctx.expression());
        }

        final TextualJMLSpecCase res = new TextualJMLSpecCase(mods, Behavior.NORMAL_BEHAVIOR);
        res.addName(new PositionedString("assert " + assertStm.text, assertStm.fileName, assertStm.pos));
        res.addEnsures(assertStm);
        res.addAssignable(new PositionedString("assignable \\strictly_nothing;", assertStm.fileName, assertStm.pos));
        res.setPosition(assertStm);
        return res;
    }

    @Override
    public Object visitBreaks_clause(JmlParser.Breaks_clauseContext ctx) {
        return super.visitBreaks_clause(ctx);
    }

    @Override
    public Object visitContinues_clause(JmlParser.Continues_clauseContext ctx) {
        return super.visitContinues_clause(ctx);
    }

    @Override
    public Object visitReturns_clause(JmlParser.Returns_clauseContext ctx) {
        return super.visitReturns_clause(ctx);
    }

    @Override
    public Object visitBreak_behavior_spec_case(JmlParser.Break_behavior_spec_caseContext ctx) {
        currentBehavior = Behavior.BREAK_BEHAVIOR;
        return accept(ctx.generic_spec_case());
    }

    @Override
    public Object visitContinue_behavior_spec_case(JmlParser.Continue_behavior_spec_caseContext ctx) {
        currentBehavior = Behavior.Continue_BEHAVIOR;
        return accept(ctx.generic_spec_case());
    }

    @Override
    public Object visitReturn_behavior_spec_case(JmlParser.Return_behavior_spec_caseContext ctx) {
        currentBehavior = Behavior.RETURN_BEHAVIOR;
        return accept(ctx.generic_spec_case());
    }

}
