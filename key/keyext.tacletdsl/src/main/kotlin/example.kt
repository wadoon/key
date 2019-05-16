import ApplyRestriction.SameUpdateLevel

val base = rules {
    val b = schemaFormula("b")
    val c = schemaFormula("c")
    val d = schemaFormula("d")
    val cutFormula = schemaFormula("cutFormula")
    val br = schemaFormula("br", rigid = true)
    val cr = schemaFormula("cr", rigid = true)
    val ALPHA = Heuristic("alpha")
    val SIMPLIFY = Heuristic("simplify")


    taclet("andLeft") {
        restriction = SameUpdateLevel
        findAntec(b `&` c)
        replaceWith("b,c ==>")
        heuristics = ALPHA
        ruleSet()
        displayname("andLefty")
    }

    taclet("insert_eqv_once_lr") {
        find("br <-> cr ==>")
        addrules {
            taclet("insert_eqv") {
                find("br")
                replaceWith("cr")
            }
        }
    }

    taclet("cut_direct") {
        restriction = SameUpdateLevel
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
        addrules {
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
        displayname("case_distinction")
    }
}

private infix fun String.`&`(right: String): String {
    return "$this & right"
}
