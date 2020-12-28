package org.key_project.ide

import javafx.scene.Node
import javafx.scene.control.TreeItem
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.ParserRuleContext
import org.key_project.ide.parser.JavaJMLLexer
import org.key_project.ide.parser.KeYLexer
import org.key_project.ide.parser.KeYParser
import org.key_project.ide.parser.KeYParserBaseVisitor
import java.nio.file.Path

abstract class Language {
    abstract val name: String
    abstract fun lexerFactory(input: CharStream): Lexer

    protected var structural: Set<Int> = setOf()
    protected var separators: Set<Int> = setOf()
    protected var literals: Set<Int> = setOf()
    protected var identifiers: Set<Int> = setOf()
    protected var specialIds: Set<Int> = setOf()
    protected var comments: Set<Int> = setOf()
    protected var docComments: Set<Int> = setOf()
    protected var datatype: Set<Int> = setOf()
    protected var control: Set<Int> = setOf()
    protected var operators: Set<Int> = setOf()
    protected var errorChar: Int = -2

    fun getStyleClass(tokenType: Int) =
        when (tokenType) {
            in separators -> "separator"
            in structural -> "structural"
            in literals -> "literal"
            in identifiers -> "identifier"
            in specialIds -> "fancy-identifier"
            in comments -> "comment"
            in docComments -> "doc-comment"
            in datatype -> "datatype"
            in control -> "control"
            in operators -> "operators"
            else -> {
                System.err.println("token type $tokenType (${javaClass.name}) is not registered for syntax highlightning.")
                ""
            }
        }

    abstract fun computeOutline(input: CharStream, editor: Editor): TreeItem<OutlineEntry>?
    abstract fun computeIssues(filename: Path?, text: String?, editor: Editor): List<IssueEntry>

}

object KeyLanguage : Language() {
    override val name: String = "KeY"
    override fun lexerFactory(input: CharStream): Lexer = KeYLexer(input)

    override fun computeOutline(input: CharStream, editor: Editor): TreeItem<OutlineEntry> {
        val p = KeYParser(CommonTokenStream(KeYLexer(input)))
        val ctx = p.file()
        val root = TreeItem(OutlineEntry(editor.title.value, editor, caretPosition = 0))
        ctx.accept(object : KeYParserBaseVisitor<Unit>() {
            val sorts = createNode("Sorts")
            val functions = createNode("Functions")
            val choices = createNode("Choices")
            val predicates = createNode("Predicates")

            override fun visitDecls(ctx: KeYParser.DeclsContext?) {
                root.isExpanded = true
                root.children.addAll(sorts, functions, choices, predicates)
                super.visitDecls(ctx)
            }

            override fun visitFunc_decl(ctx: KeYParser.Func_declContext) {
                val text = "${ctx.func_name.text} : ${ctx.sortId().text}"
                val item = createNode(text, ctx)
                functions.children.add(item)
            }

            override fun visitPred_decl(ctx: KeYParser.Pred_declContext) {
                val item = createNode(ctx.funcpred_name().text, ctx.funcpred_name())
                predicates.children.add(item)
            }

            override fun visitOne_sort_decl(ctx: KeYParser.One_sort_declContext) {
                for (simpleIdentDot in ctx.sortIds.simple_ident_dots()) {
                    sorts.children.add(createNode(simpleIdentDot.text, simpleIdentDot))
                }
            }

            override fun visitOptions_choice(ctx: KeYParser.Options_choiceContext?) {
                super.visitOptions_choice(ctx)
            }

            override fun visitRulesOrAxioms(ctx: KeYParser.RulesOrAxiomsContext) {
                addNode(
                    if (null != ctx.AXIOMS()) "Axioms" else "Rules",
                    ctx,
                    children = ctx.taclet().map { createNode(it.name.text, it) })

            }

            override fun visitProblem(ctx: KeYParser.ProblemContext) {
                addNode("Problem", ctx)
            }

            private fun addNode(
                text: String,
                ctx: ParserRuleContext? = null,
                graphic: Node? = null,
                children: List<TreeItem<OutlineEntry>>? = null
            ): TreeItem<OutlineEntry> {
                return createNode(text, ctx, graphic, children).also { root.children.add(it) }
            }

            private fun createNode(
                text: String,
                ctx: ParserRuleContext? = null,
                graphic: Node? = null,
                children: List<TreeItem<OutlineEntry>>? = null
            ): TreeItem<OutlineEntry> {
                val oe = OutlineEntry(text, editor, ctx?.let { ctx.start?.startIndex })
                val t = TreeItem(oe)
                t.graphic = graphic
                if (children != null) t.children.setAll(children)
                t.isExpanded=true
                return t
            }

            override fun visitOneJavaSource(ctx: KeYParser.OneJavaSourceContext) {
                createNode("Java Source", ctx,
                    children = ctx.string_value().map { createNode(it.text, ctx = it) })
                    .also { root.children.add(it) }
            }
        })
        return root
    }

    override fun computeIssues(filename: Path?, text: String?, editor: Editor): List<IssueEntry> {
        return listOf(IssueEntry("Test entry", "test", 0))
    }

    init {
        structural = setOf(
            KeYLexer.SORTS, KeYLexer.FUNCTIONS, KeYLexer.PREDICATES, KeYLexer.TRANSFORMERS,
            KeYLexer.RULES, KeYLexer.JAVASOURCE, KeYLexer.CLASSPATH, KeYLexer.BOOTCLASSPATH, KeYLexer.CHOOSECONTRACT,
            KeYLexer.PROBLEM, KeYLexer.CONTRACTS, KeYLexer.AXIOMS
        )

        datatype = setOf()

        literals = setOf(
            KeYLexer.BIN_LITERAL, KeYLexer.HEX_LITERAL, KeYLexer.CHAR_LITERAL,
            KeYLexer.NUM_LITERAL, KeYLexer.QUOTED_STRING_LITERAL, KeYLexer.STRING_LITERAL
        )

        control = setOf()

        operators = setOf(
            KeYLexer.ADD, KeYLexer.ADDPROGVARS, KeYLexer.ADDRULES,
            KeYLexer.AND, KeYLexer.OR, KeYLexer.IMP, KeYLexer.NOT,
            KeYLexer.NOTFREEIN, KeYLexer.NOT_, KeYLexer.NOT_EQUALS, KeYLexer.EQUALS,
            KeYLexer.AT
        )

        separators = setOf(
            KeYLexer.DOT, KeYLexer.LPAREN, KeYLexer.RPAREN, KeYLexer.RBRACE, KeYLexer.RBRACE,
            KeYLexer.LBRACE, KeYLexer.LBRACKET
        )

        identifiers = setOf(KeYLexer.IDENT)
        comments = setOf(KeYLexer.ML_COMMENT, KeYLexer.SL_COMMENT)
        docComments = setOf(KeYLexer.DOC_COMMENT)
        errorChar = KeYLexer.ERROR_CHAR
    }
}

object JavaLanguage : Language() {
    override val name: String = "Java+Jml"

    override fun lexerFactory(input: CharStream): Lexer = JavaJMLLexer(input)
    override fun computeOutline(input: CharStream, editor: Editor): TreeItem<OutlineEntry> {
        val root = TreeItem(OutlineEntry(editor.title.value, editor, caretPosition = 0))
        return root
    }

    override fun computeIssues(filename: Path?, text: String?, editor: Editor): List<IssueEntry> {
        return listOf(IssueEntry("Test entry", "test", 0))
    }

    init {
        structural = setOf(
            JavaJMLLexer.CLASS,
            JavaJMLLexer.IF,
            JavaJMLLexer.ELSE,
            JavaJMLLexer.WHILE,
            JavaJMLLexer.FOR,
            JavaJMLLexer.INTERFACE,
            JavaJMLLexer.PUBLIC,
            JavaJMLLexer.PRIVATE,
            JavaJMLLexer.PROTECTED,
            JavaJMLLexer.PURE,
            JavaJMLLexer.STRICTLY_PURE,
            JavaJMLLexer.NULLABLE,
            JavaJMLLexer.NULLABLE_BY_DEFAULT,
            JavaJMLLexer.NON_NULL
        )

        datatype = setOf(
            JavaJMLLexer.INT,
            JavaJMLLexer.BOOLEAN,
            JavaJMLLexer.FLOAT,
            JavaJMLLexer.DOUBLE,
            JavaJMLLexer.VOID,
        )

        separators = setOf(
            JavaJMLLexer.RBRACE,
            JavaJMLLexer.LBRACE,
            JavaJMLLexer.RPAREN,
            JavaJMLLexer.LPAREN,
            JavaJMLLexer.LBRACK,
            JavaJMLLexer.RBRACK,
            JavaJMLLexer.COLON,
            JavaJMLLexer.COMMA
        )
        literals = setOf(
            JavaJMLLexer.BINARY_LITERAL,
            JavaJMLLexer.BINARY_LITERAL,
            JavaJMLLexer.FLOAT_LITERAL,
            JavaJMLLexer.HEX_FLOAT_LITERAL,
            JavaJMLLexer.BOOL_LITERAL,
            JavaJMLLexer.CHAR_LITERAL,
            JavaJMLLexer.STRING_LITERAL,
            JavaJMLLexer.NULL_LITERAL
        )
        identifiers = setOf(JavaJMLLexer.IDENTIFIER)
        comments = setOf(JavaJMLLexer.LINE_COMMENT, JavaJMLLexer.COMMENT_START)
    }
}

