import de.uka.ilkd.key.java.Services
import de.uka.ilkd.key.logic.*
import de.uka.ilkd.key.logic.op.*
import de.uka.ilkd.key.logic.op.Function
import de.uka.ilkd.key.logic.sort.Sort
import de.uka.ilkd.key.rule.*
import de.uka.ilkd.key.rule.RewriteTaclet.*
import de.uka.ilkd.key.rule.tacletbuilder.*
import org.key_project.util.collection.*
import java.lang.IllegalStateException
import java.util.*
import kotlin.collections.HashSet

enum class ApplyRestriction(val flag: Int) {
    NONE(RewriteTaclet.NONE),
    SameUpdateLevel(SAME_UPDATE_LEVEL),
    InSequentState(IN_SEQUENT_STATE),
    AntecedentPolarity(ANTECEDENT_POLARITY),
    SuccedentPolarity(SUCCEDENT_POLARITY)
}

class TacletBuilder(val name: String) {
    private var isAntec: Boolean = false
    private var isSucc: Boolean = false
    private var findTerm: String? = null;
    private var restriction: EnumSet<ApplyRestriction> = EnumSet.noneOf(ApplyRestriction::class.java)
    private val branches = arrayListOf<Branch>()
    private val newRules = TacletBase()


    var heuristics: Heuristic? = null
    var displayName = name

    fun findAntec(s: String) {
        isAntec = true
        findTerm = s
    }

    fun findSucc(s: String) {
        isSucc = true
        findTerm = s
    }

    fun find(s: String) {
        findTerm = s
    }


    fun branch(apply: Branch.() -> Unit): Branch {
        return Branch().apply(apply).also { branches.add(it) }
    }

    fun replaceWith(substitution: String, apply: Branch.() -> Unit = {}) = branch(apply).also { it.replaceWith = substitution }


    fun displayName(s: String) {
        displayName = s
    }

    fun addRules(apply: TacletBase.() -> Unit) {
        newRules.apply(apply)
    }

    fun restriction(r: ApplyRestriction) {
        restriction = EnumSet.of(r)
    }

    fun addRestriction(i: ApplyRestriction) {
        restriction.add(i)
        /*
            RewriteTaclet.IN_SEQUENT_STATE
            RewriteTaclet.SAME_UPDATE_LEVEL
            RewriteTaclet.ANTECEDENT_POLARITY
            RewriteTaclet.SUCCEDENT_POLARITY
         */
    }

    fun build(ctx: Context): Taclet {
        val subTaclets = newRules.build()
        val term = findTerm?.let { ctx.parse(it) }
        val assummptions: List<Term> = arrayListOf()
        val apprestr = restriction.map { it.flag }.reduce { acc, i -> acc or i }


        val builder = when {
            isAntec && isSucc -> throw IllegalStateException()

            isSucc -> SuccTacletBuilder().also {
                it.find = term
                it.setIgnoreTopLevelUpdates(apprestr and IN_SEQUENT_STATE == 0)
            }

            isAntec -> AntecTacletBuilder().also {
                it.find = term
                it.setIgnoreTopLevelUpdates(apprestr and IN_SEQUENT_STATE == 0)
            }

            else -> {
                RewriteTacletBuilder<RewriteTaclet>().also {
                    it.find = term
                    it.setApplicationRestriction(apprestr)
                }
            }
        }
        builder.name = Name(name)

        branches.forEach { it ->
            val addSeq: Sequent? = ctx.parseSeq(it.addedSequent)
            val addedRules = ImmutableList.fromList(it.tacletBuilders.map { it.build(ctx) })
            val pvs = DefaultImmutableSet.nil<SchemaVariable>() //TODO
            val goal = when {
                it.replaceWith == null -> TacletGoalTemplate(addSeq, addedRules, pvs)
                isAntec or isSucc ->
                    AntecSuccTacletGoalTemplate(addSeq, addedRules, ctx.parseSeq(it.replaceWith!!), pvs)
                else -> RewriteTacletGoalTemplate(addSeq, addedRules, ctx.parse(it.replaceWith!!), pvs)
            }
            goal.setName(it.label)
            builder.addTacletGoalTemplate(goal)
            //TODO if (soc != null) b.addGoal2ChoicesMapping(gt, soc)
        }


        val applPart: TacletApplPart
        val goalTemplates: ImmutableList<TacletGoalTemplate>
        val heuristics: ImmutableList<RuleSet>
        val attrs: TacletAttributes
        val ignoreTopLevelUpdates: Boolean = false
        val prefixMap: ImmutableMap<SchemaVariable, TacletPrefix>
        val choices: ImmutableSet<Choice>? = null
        val tacletAnnotations: ImmutableSet<TacletAnnotation> = ImmutableSet.fromSet(HashSet())

        return builder.taclet
    }
}


class Context {
    lateinit var services: Services
    val termFactory: TermFactory
        get() = services.termFactory

    val namespaces: NamespaceSet = NamespaceSet()

    val sorts: Namespace<Sort>
        get() = namespaces.sorts()

    val functions: Namespace<Function>
        get() = namespaces.functions()

    val programVariables: Namespace<IProgramVariable>
        get() = namespaces.programVariables()

    val variables: Namespace<QuantifiableVariable>
        get() = namespaces.variables()

    val ruleSets: Namespace<RuleSet>
        get() = namespaces.ruleSets()

    val choices: Namespace<Choice>
        get() = namespaces.choices()

    val schemaVariables: Namespace<SchemaVariable> = Namespace()

    fun parse(findTerm: String): Term {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    fun parseSeq(addedSequent: String?): Sequent? = addedSequent?.let { parseSeq(it) }
}

class Branch {
    val newRules = TacletBase()
    var addedSequent: String? = null
    var replaceWith: String? = null
    //val addTerms: MutableList<String> = arrayListOf()
    var label: String? = null

    var tacletBuilders: MutableList<TacletBuilder> = arrayListOf()

    fun add(seq: String) {
        addedSequent = seq
        //  addTerms += seq
    }

    fun addRules(apply: TacletBase.() -> Unit) {
        newRules.apply(apply)
    }
}

class TacletBase {
    private val context: Context
        get() {
            return Context()
        }

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

    fun build() = taclets.map { it.build(context) }
}

data class Heuristic(val name: String)

fun rules(apply: TacletBase.() -> Unit): TacletBase {
    return TacletBase().apply(apply)
}


