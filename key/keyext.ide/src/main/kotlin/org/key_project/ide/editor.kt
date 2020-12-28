package org.key_project.ide

import javafx.beans.binding.Bindings
import javafx.beans.property.SimpleBooleanProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.scene.control.TreeItem
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.Lexer
import org.fxmisc.flowless.VirtualizedScrollPane
import org.fxmisc.richtext.CodeArea
import org.fxmisc.richtext.LineNumberFactory
import org.fxmisc.richtext.model.StyleSpans
import org.fxmisc.richtext.model.StyleSpansBuilder
import org.key_project.ide.parser.JavaJMLLexer
import org.key_project.ide.parser.KeYLexer
import org.key_project.ide.parser.KeYParser
import org.key_project.ide.parser.KeYParserBaseVisitor
import org.reactfx.EventStreams
import tornadofx.getValue
import tornadofx.setValue
import java.nio.file.Path
import java.time.Duration
import java.util.*
import kotlin.io.path.ExperimentalPathApi
import kotlin.io.path.extension

@OptIn(ExperimentalPathApi::class)
object Editors {
    fun getLanguageForFilename(file: Path) = getEditorForSuffix(file.extension)
    fun getEditorForSuffix(suffix: String): Language? =
        when (suffix) {
            "key" -> KeyLanguage
            "java", "jml" -> JavaLanguage
            else -> null
        }
}


open class Editor(val ctx: Context) : Controller {
    val editor = CodeArea("")
    val scrollPane = VirtualizedScrollPane(editor)
    override val ui = scrollPane

    val dirtyProperty = SimpleBooleanProperty(this, "dirty", false)
    var dirty by dirtyProperty

    val filenameProperty = SimpleObjectProperty<Path>(this, "filename", null)
    var filename by filenameProperty

    val languageProperty = SimpleObjectProperty<Language>(this, "language", null)
    var language by languageProperty

    val title = Bindings.createStringBinding(
        { (filename?.fileName?.toString() ?: "unknown_file") + (if (dirty) "*" else "") },
        dirtyProperty,
        filenameProperty
    )

    init {
        editor.paragraphGraphicFactory = LineNumberFactory.get(editor) //{ String.format("%03d", it) }
        editor.isLineHighlighterOn = true

        filenameProperty.addListener { _, _, new ->
            language = Editors.getLanguageForFilename(new)
        }

        editor.textProperty().addListener { _, _, newText: String ->
            dirty = true
            onTextLightComputation()
        }

        languageProperty.addListener { _, _, new ->
            onTextLightComputation()
            onTextChangeHeavyComputation()
        }

        EventStreams.changesOf(editor.textProperty())
            .successionEnds(Duration.ofMillis(500)) //wait 500ms before responds
            .forgetful()
            .subscribe { onTextChangeHeavyComputation() }
    }

    private fun onTextChangeHeavyComputation() {
        val text = editor.text
        language?.let { language ->
            if (text.isNotEmpty()) {
                language.computeOutline(CharStreams.fromString(editor.text), this)?.let { root ->
                    ctx.get<FileOutline>().outlineTree.root = root
                }

                language.computeIssues(filename, editor.text, this).let { root ->
                    ctx.get<IssueList>().view.items.setAll(root)
                }
            }
        }
    }

    private fun onTextLightComputation() {
        language?.also { lang ->
            editor.setStyleSpans(0, computeHighlighting(lang))
        }
    }


    fun computeHighlighting(language: Language): StyleSpans<Collection<String>>? {
        val text = editor.text
        val spansBuilder = StyleSpansBuilder<Collection<String>>()
        val lexer = language.lexerFactory(CharStreams.fromString(text))
        do {
            val tok = lexer.nextToken()
            if (tok.type == -1) break
            val typ = language.getStyleClass(tok.type)// lexer.vocabulary.getSymbolicName(tok.type)
            spansBuilder.add(Collections.singleton(typ), tok.text.length)
        } while (tok.type != -1)
        return spansBuilder.create()
    }
}

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
            val sorts = TreeItem(OutlineEntry("Sorts", editor))
            val functions = TreeItem(OutlineEntry("Functions", editor))
            val choices = TreeItem(OutlineEntry("Choices", editor))
            val predicates = TreeItem(OutlineEntry("Predicates", editor))
            val rules = TreeItem(OutlineEntry("Rules", editor))
            val axioms = TreeItem(OutlineEntry("Axioms", editor))

            override fun visitDecls(ctx: KeYParser.DeclsContext?) {
                root.isExpanded=true
                sorts.isExpanded = true
                functions.isExpanded = true
                choices.isExpanded = true
                predicates.isExpanded = true
                rules.isExpanded = true
                axioms.isExpanded = true
                root.children.addAll(sorts, functions, choices, predicates, rules, axioms)
                super.visitDecls(ctx)
            }

            override fun visitFunc_decl(ctx: KeYParser.Func_declContext) {
                val text = "${ctx.func_name.text} : ${ctx.sortId().text}"
                val item = TreeItem(OutlineEntry(text, editor))
                functions.children.add(item)
            }

            override fun visitPred_decl(ctx: KeYParser.Pred_declContext) {
                val item = TreeItem(OutlineEntry(ctx.funcpred_name().text, editor))
                functions.children.add(item)
            }

            override fun visitOne_sort_decl(ctx: KeYParser.One_sort_declContext) {
                for (simpleIdentDot in ctx.sortIds.simple_ident_dots()) {
                    val item = TreeItem(OutlineEntry(simpleIdentDot.text, editor))
                    functions.children.add(item)
                }
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

