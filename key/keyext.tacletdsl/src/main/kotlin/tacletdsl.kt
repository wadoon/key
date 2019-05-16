import de.uka.ilkd.key.logic.Choice
import de.uka.ilkd.key.logic.Term
import de.uka.ilkd.key.logic.op.SchemaVariable
import de.uka.ilkd.key.rule.*
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate
import org.key_project.util.collection.ImmutableList
import org.key_project.util.collection.ImmutableMap
import org.key_project.util.collection.ImmutableSet

enum class ApplyRestriction {
    NONE, SameUpdateLevel, InSequentState,
    AntecedentPolarity, SuccedentPolarity
}

class TacletBuilder(val name: String) {
    var restriction: ApplyRestriction = ApplyRestriction.NONE

    fun findAntec(s: String) {
    }

    fun findSucc(s: String) {
    }

    fun findAny(s: String) {
    }

    fun find(s: String) {

    }

    val replaceWithBranches = arrayListOf<Branch>()

    fun replaceWith(s: String, apply: Branch.() -> Unit = {}) {
        Branch(s).apply(apply).also {
            replaceWithBranches.add(it)
        }
    }

    var heuristics: Heuristic? = null

    fun displayname(s: String) {

    }

    fun addrules(apply: TacletBase.() -> Unit) {
        TacletBase().apply(apply)
    }

    fun build(): Taclet {
        val applPart: TacletApplPart
        val goalTemplates: ImmutableList<TacletGoalTemplate>
        val heuristics: ImmutableList<RuleSet>
        val attrs: TacletAttributes
        val find: Term;
        val ignoreTopLevelUpdates: Boolean = false
        val prefixMap: ImmutableMap<SchemaVariable, TacletPrefix>
        val choices: ImmutableSet<Choice>? = null
        val tacletAnnotations: ImmutableSet<TacletAnnotation> = ImmutableSet.fromSet(HashSet())

        val taclet = AntecTaclet(name,
                applPart, goalTemplates, heuristics, attrs, find, ignoreTopLevelUpdates,
                prefixMap, choices, tacletAnnotations);


    }
}

class Branch(val s: String) {
    fun add(s: String) {
    }

    var label: String = ""
}

class TacletBase() {
    val taclets: MutableList<TacletBuilder> = arrayListOf()

    fun taclet(name: String, apply: TacletBuilder.() -> Unit): TacletBuilder {
        return TacletBuilder(name).apply(apply).also { taclets.add(it) }
    }

    fun formula(s: String): String {
        return s
    }

    fun schemaFormula(name: String, rigid: Boolean = false): String {
        return name
    }

    fun build() = taclets.map { it.build() }
}

data class Heuristic(val name: String)

fun rules(apply: TacletBase.() -> Unit): TacletBase {
    return TacletBase().apply(apply)
}


