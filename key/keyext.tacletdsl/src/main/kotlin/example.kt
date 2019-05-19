import ApplyRestriction.SameUpdateLevel

/*
class Operator<A, B, C>()
sealed class Term<S>() {}
data class Var<S>(val name: String, val sort: S) : Term<S>()
data class Op<A, B, S>(val left: Term<A>, val right: Term<B>,
                       val operator: Operator<A, B, S>) : Term<S>()
val equal = Operator<Any, Any, Boolean>()
val term = Op(Var("name", Any()),
        Var("name", Any()), equal)
*/

val ALPHA = Heuristic("alpha")
val SIMPLIFY = Heuristic("simplify")


val base = rules {
    val b = schemaFormula("b")
    val c = schemaFormula("c")
    val d = schemaFormula("d")
    val cutFormula = schemaFormula("cutFormula")
    val br = schemaFormula("br", rigid = true)
    val cr = schemaFormula("cr", rigid = true)

    taclet("andLeft") {
        restriction(SameUpdateLevel)
        findAntec(b `&` c)
        replaceWith("b,c ==>")
        heuristics = ALPHA
        displayName = "andLefty"
    }

    taclet("insert_eqv_once_lr") {
        findAntec("br <-> cr ==>")
        addRules {
            taclet("insert_eqv") {
                find("br")
                replaceWith("cr")
            }
        }
    }

    taclet("cut_direct") {
        restriction(SameUpdateLevel)
        find("cutFormula")

        replaceWith("true") {
            label = "CUT: #cutFormula TRUE"
            add("cutFormula ==>")
        }

        replaceWith("false") {
            label = "CUT: #cutFormula FALSE"
            add("==> cutFormula")
        }
        heuristics = Heuristic("cut_direct")
    }

    taclet("case_distinction_l") {
        find("b ==>")
        addRules {
            taclet("to_true") {
                find("b ==>")
                replaceWith("true ==>")
                heuristics = SIMPLIFY
            }
            taclet("to_false") {}
            find("b ==>")
            replaceWith("false ==>")
            heuristics = SIMPLIFY
        }
        displayName("case_distinction")
    }
}

private infix fun String.`&`(right: String): String {
    return "$this & right"
}

fun main() {
    val taclets = base.build()
    println(taclets)
}