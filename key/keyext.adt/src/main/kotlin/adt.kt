import de.uka.ilkd.key.adt.ADTLangBaseVisitor
import de.uka.ilkd.key.adt.ADTLangLexer
import de.uka.ilkd.key.adt.ADTLangParser
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.PrintStream
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (5/5/21)
 */

fun main(args: Array<String>) {
    require(args.isNotEmpty())
    val ctx = parse(args.first())
    val t = Translator()
    ctx.accept(t)
    t.print(System.out)
}

fun parse(filename: String): ADTLangParser.FileContext {
    val lexer = ADTLangLexer(CharStreams.fromFileName(filename))
    val parser = ADTLangParser(CommonTokenStream(lexer))
    val ctx = parser.file()
    require(parser.numberOfSyntaxErrors == 0)
    return ctx
}

class Translator : ADTLangBaseVisitor<Unit>() {
    val declaredTypes = HashMap<String, HashMap<String, List<String>>>()


    val sorts = StringBuilder()
    val functions = StringBuilder()
    val axioms = StringBuilder()
    val rules = StringBuilder()

    lateinit var currentSort: String

    override fun visitFile(ctx: ADTLangParser.FileContext) = ctx.theory().forEach { it.accept(this) }
    override fun visitTheory(ctx: ADTLangParser.TheoryContext) {
        ctx.datatype().forEach { it.accept(this) }
        ctx.function().forEach { it.accept(this) }
    }

    override fun visitDatatype(ctx: ADTLangParser.DatatypeContext) {
        currentSort = ctx.id().text
        sorts.append("$currentSort;\n")
        ctx.constructor().forEach { it.accept(this) }

        var decls = ""
        var cidx = 0;
        val deconstructed =
            ctx.constructor().joinToString("\n&") {
                ++cidx;
                val baseName = it.name.text
                val args = it.a.map { it.text }
                if (args.isEmpty()) {
                    "{ \\subst lv; $baseName } phi"
                } else {
                    val parameterNames = args.mapIndexed { idx, it ->
                        "x_${cidx}_${idx}";
                    }
                    parameterNames.zip(args).forEach { (v, s) ->
                        decls += "\\schemaVar \\variable $s $v;\n"
                    }

                    val quants = parameterNames.joinToString(" ") { v ->
                        "\\forall $v;"
                    }
                    "$quants (phi -> {\\subst lv; $baseName(${parameterNames.joinToString(", ")})} phi)"
                }
            }
        //\varcond(\notFreeIn(av, phi))?

        axioms.append(
            """
${currentSort}_induction {
    \schemaVar \formula phi;
    \schemaVar \variable $currentSort lv;
    $decls
    
    \find( ==> \forall lv; phi )
    \replacewith( ==> $deconstructed)
};
        }"""
        )
    }

    override fun visitConstructor(ctx: ADTLangParser.ConstructorContext) {
        val name = ctx.name.text
        val a =
            if (ctx.a.isEmpty()) Collections.emptyList()
            else ctx.a.map { it.text }
        val args = a.joinToString(", ", "(", ")")
        functions.append("\\unique $currentSort $name$args;\n")
        registerConstructor(currentSort, name, a)
    }

    private fun registerConstructor(currentSort: String, name: String, args: List<String>) {
        declaredTypes.computeIfAbsent(currentSort) { hashMapOf() }[name] = args
    }

    var ruleIdx = 0;
    override fun visitFunction(ctx: ADTLangParser.FunctionContext) {
        ++ruleIdx;
        val ruleName = ctx.name.text + ruleIdx

        axioms.append("""
$ruleName { length(nil) = 0 };
        """.trimIndent())
        /*
        length_cons {
            \forall List l; \forall any a; length(cons(a, l)) = 1 + length(l)
        };*/
        super.visitFunction(ctx)
    }


    override fun visitId(ctx: ADTLangParser.IdContext?) {
        super.visitId(ctx)
    }

    fun print(out: PrintStream) {
        out.print(
            """
\sorts {
$sorts}

\functions {
$functions}

\axioms {
$axioms
}

\rules {
$rules
}"""
        )
    }
}