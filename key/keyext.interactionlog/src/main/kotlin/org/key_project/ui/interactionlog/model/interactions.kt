package org.key_project.ui.interactionlog.model

import com.fasterxml.jackson.annotation.JsonIgnore
import de.uka.ilkd.key.api.ProofMacroApi
import de.uka.ilkd.key.control.InteractionListener
import de.uka.ilkd.key.logic.PosInOccurrence
import de.uka.ilkd.key.logic.Sequent
import de.uka.ilkd.key.logic.Term
import de.uka.ilkd.key.macros.ProofMacro
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo
import de.uka.ilkd.key.macros.scripts.EngineState
import de.uka.ilkd.key.macros.scripts.RuleCommand
import de.uka.ilkd.key.pp.LogicPrinter
import de.uka.ilkd.key.proof.Goal
import de.uka.ilkd.key.proof.Node
import de.uka.ilkd.key.proof.Proof
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo
import de.uka.ilkd.key.rule.RuleApp
import de.uka.ilkd.key.rule.TacletApp
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl
import org.key_project.ui.interactionlog.algo.LogPrinter
import org.key_project.ui.interactionlog.api.Interaction
import org.key_project.util.RandomName
import org.key_project.util.collection.ImmutableSLList
import java.awt.Color
import java.io.IOException
import java.io.Serializable
import java.io.StringWriter
import java.lang.ref.WeakReference
import java.util.*


/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
class InteractionLog {
    @get:JsonIgnore
    @set:JsonIgnore
    @field:JsonIgnore
    var proof: WeakReference<Proof> = WeakReference<Proof>(null)

    @get:JsonIgnore
    @field:JsonIgnore
    val listeners = arrayListOf<() -> Unit>()

    val name: String
    var created = Date()

    private val _interactions: MutableList<Interaction> = ArrayList()

    val interactions: List<Interaction>
        get() = _interactions


    fun add(interaction: Interaction) = _interactions.add(interaction)
    fun remove(interaction: Interaction) = _interactions.remove(interaction)
    fun remove(index: Int) = _interactions.removeAt(index)

    @JvmOverloads
    constructor(name: String = RandomName.getRandomName()) {
        this.name = name
    }

    constructor(proof: Proof) {
        val pos = Math.min(proof.name().toString().length, 25)
        name = (RandomName.getRandomName(" ")
                + " (" + proof.name().toString().substring(0, pos) + ")")
        this.proof = WeakReference(proof)
    }

    override fun toString(): String {
        return name
    }
}


abstract class NodeInteraction(@Transient var serialNr: Int? = null) : Interaction() {
    var nodeId: NodeIdentifier? = null

    constructor(node: Node) : this(node.serialNr()) {
        this.nodeId = NodeIdentifier.get(node)
    }

    fun getNode(proof: Proof): Node {
        return nodeId!!.findNode(proof).orElse(null)
    }
}


/**
 * @author Alexander Weigl
 */
class MacroInteraction() : NodeInteraction() {
    var macroName: String? = null
    var macro: ProofMacro? = null
    var pos: PosInOccurrence? = null
    var info: String? = null
    var openGoalSerialNumbers: List<Int>? = null
    var openGoalNodeIds: List<NodeIdentifier>? = null

    override val markdown: String
        get() = """
        ## Applied macro $macro

        ```
        $info
        ```
        """.trimIndent()

    override val proofScriptRepresentation: String
        get() = "macro $macro;\n"

    constructor(node: Node, macro: ProofMacro, posInOcc: PosInOccurrence?, info: ProofMacroFinishedInfo) : this() {
        this.info = info.toString()
        macroName = macro.scriptCommandName
        pos = posInOcc
        val openGoals = if (info.proof != null)
            info.proof.openGoals()
        else
            ImmutableSLList.nil()
        this.openGoalSerialNumbers = openGoals.map { g -> g.node().serialNr() }
        this.openGoalNodeIds = openGoals.map { g -> NodeIdentifier.get(g.node()) }
    }

    override fun toString(): String {
        return macroName ?: "n/a"
    }

    @Throws(Exception::class)
    override fun reapplyStrict(uic: AbstractMediatorUserInterfaceControl, goal: Goal) {
        val macro = ProofMacroApi().getMacro(macroName)
        val pio = pos
        if (macro != null) {
            if (!macro.canApplyTo(goal.node(), pio)) {
                throw IllegalStateException("Macro not applicable")
            }

            try {
                macro.applyTo(uic, goal.node(), pio, uic)
            } catch (e: Exception) {
                e.printStackTrace()
            }

        }
    }

    companion object {
        private val serialVersionUID = 1L
    }
}


/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
class NodeIdentifier() : Serializable {
    var treePath: MutableList<Int> = ArrayList()

    var branchLabel: String? = null

    var serialNr: Int = 0

    constructor(seq: List<Int>) : this() {
        this.treePath.addAll(seq)
    }

    override fun toString(): String {
        return treePath.stream()
                .map { it.toString() }
                .reduce("") { a, b -> a + b } +
                " => " + serialNr
    }


    fun findNode(proof: Proof): Optional<Node> {
        return findNode(proof.root())
    }

    fun findNode(node: Node): Optional<Node> {
        var n = node
        for (child in treePath) {
            if (child <= n.childrenCount()) {
                n = n.child(child)
            } else {
                return Optional.empty()
            }
        }
        return Optional.of(n)
    }

    companion object {
        private const val serialVersionUID = 7147788921672163642L

        operator fun get(g: Goal): NodeIdentifier {
            return get(g.node())
        }

        operator fun get(node: Node): NodeIdentifier {
            var n: Node? = node
            val list = LinkedList<Int>()
            do {
                val parent = n?.parent()
                if (parent != null) {
                    list.add(0, parent.getChildNr(n))
                }
                n = parent
            } while (n != null)
            val ni = NodeIdentifier(list)
            ni.branchLabel = LogPrinter.getBranchingLabel(n)
            return ni
        }
    }
}

class PruneInteraction() : NodeInteraction() {
    constructor(node: Node) : this() {
        serialNr = node.serialNr()
        nodeId = NodeIdentifier.get(node)
    }

    override val markdown: String
        get() = """
                ## Prune

                * **Date**: $created
                * Prune to node: `$nodeId`
                """

    override val proofScriptRepresentation: String
        get() = "prune $nodeId\n"

    override fun toString(): String {
        return "prune"
    }

    @Throws(Exception::class)
    override fun reapplyStrict(uic: AbstractMediatorUserInterfaceControl, goal: Goal) {
        nodeId?.findNode(goal.proof())
                ?.get()
                ?.also { goal.proof().pruneProof(it) }
    }

    companion object {
        private val serialVersionUID = -8499747129362589793L
    }
}


/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
class OccurenceIdentifier {
    var path: Array<Int>? = null
    var term: String? = null
    var toplevelTerm: String? = null
    var termHash: Int = 0
    var isAntec: Boolean = false

    override fun toString(): String {
        if (path == null) {
            return " @toplevel"
        }
        return if (path!!.size != 0) {
            term + " under " + toplevelTerm + "(Path: " + Arrays.toString(path) + ")"
        } else {
            term!! + " @toplevel"
        }
    }

    fun rebuildOn(goal: Goal): PosInOccurrence? {
        val seq = goal.node().sequent()
        return rebuildOn(seq)
    }

    private fun rebuildOn(seq: Sequent): PosInOccurrence? {
        //TODO
        return null
    }

    companion object {

        operator fun get(p: PosInOccurrence?): OccurenceIdentifier {
            if (p == null)
                return OccurenceIdentifier()

            val indices = ArrayList<Int>()
            val iter = p.iterator()
            while (iter.next() != -1) {
                indices.add(iter.child)
            }

            val occ = OccurenceIdentifier()
            occ.path = indices.toTypedArray()
            occ.term = iter.subTerm.toString()
            occ.termHash = iter.subTerm.hashCode()
            occ.toplevelTerm = p.topLevel().subTerm().toString()
            occ.isAntec = p.isInAntec
            return occ
        }
    }
}


class UserNoteInteraction() : Interaction() {
    var note: String = ""

    override val markdown: String
        get() = """
                ## Note
                
                **Date**: $created 
                
                > ${note.replace("\n", "\n> ")}
                """.trimIndent()

    init {
        graphicalStyle.backgroundColor = Color.red.brighter().brighter().brighter()
    }

    constructor(note: String) : this() {
        this.note = note
    }

    override fun toString(): String {
        return note
    }

    companion object {
        private val serialVersionUID = 1L
    }
}


class SettingChangeInteraction() : Interaction() {
    var savedSettings: Properties? = null

    var type: InteractionListener.SettingType? = null

    var message: String? = null

    override val markdown: String
        get() {
            val writer = StringWriter()
            try {
                savedSettings?.store(writer, "")
            } catch (e: IOException) {
                e.printStackTrace()
            }

            return """
            # Setting changed: ${type?.name}

            **Date**: $created

            ```
            $writer
            ```
            """.trimIndent()
        }

    constructor(settings: Properties, type: InteractionListener.SettingType) : this() {
        graphicalStyle.backgroundColor = Color.WHITE
        graphicalStyle.foregroundColor = Color.gray
        this.type = type
        this.savedSettings = settings
    }

    override fun toString(): String {
        return (if (message != null) message!! + " : " else "") + type
    }

    @Throws(Exception::class)
    override fun reapplyStrict(uic: AbstractMediatorUserInterfaceControl, goal: Goal) {
        val settings = goal.proof().settings
        when (type) {
            InteractionListener.SettingType.SMT -> settings.smtSettings.readSettings(savedSettings)
            InteractionListener.SettingType.CHOICE -> settings.choiceSettings.readSettings(savedSettings)
            InteractionListener.SettingType.STRATEGY -> settings.strategySettings.readSettings(savedSettings)
        }
    }

    companion object {
        private val serialVersionUID = 1L
    }
}


class AutoModeInteraction() : Interaction() {
    // copined from ApplyStrategyInfo info
    var infoMessage: String? = null
    var timeInMillis: Long = 0
    var appliedRuleAppsCount = 0;
    var errorMessage: String? = null
    var nrClosedGoals = 0

    //var info: ApplyStrategyInfo? = null

    var initialNodeIds: List<NodeIdentifier> = arrayListOf()
    var openGoalNodeIds: List<NodeIdentifier> = arrayListOf()

    override val markdown: String
        get() {
            val initialNodes = initialNodeIds.joinToString("\n") { nr -> "  * `$nr`" }
            val finalNodes = openGoalNodeIds.joinToString("\n") { nr -> "  * `$nr`" }

            return """
            ## Apply auto strategy
            
            **Date**: $created
    
            * Started on node:
            $initialNodes 
            
            ${if (openGoalNodeIds.isEmpty()) "* **Closed all goals**"
            else "* Finished on nodes:"}}
            $finalNodes

            * Provided Macro info:
              * Info message: $infoMessage
              * Time $timeInMillis ms
              * Applied rules: $appliedRuleAppsCount 
              * Error message: $errorMessage
              * Closed goals $nrClosedGoals
            """.trimIndent()
        }

    override val proofScriptRepresentation: String
        get() = "auto;%n"

    constructor(initialNodes: List<Node>, info: ApplyStrategyInfo) : this() {
        infoMessage = info.reason()
        timeInMillis = info.time
        appliedRuleAppsCount = info.appliedRuleApps;
        errorMessage = info.exception?.message
        nrClosedGoals = info.closedGoals
        this.initialNodeIds = initialNodes.map { NodeIdentifier.get(it) }
        val openGoals = info.proof.openGoals()
        this.openGoalNodeIds = openGoals.map { NodeIdentifier.get(it) }
    }

    override fun toString(): String {
        return "Auto Mode"
    }

    @Throws(Exception::class)
    override fun reapplyStrict(uic: AbstractMediatorUserInterfaceControl, goal: Goal) {
        uic.proofControl.startAutoMode(goal.proof(), goal.proof().openGoals(), uic)
    }

    companion object {
        private val serialVersionUID = 3650173956594987169L
    }
}


/**
 * @author weigl
 */
class RuleInteraction() : NodeInteraction() {
    var ruleName: String? = null
    var posInOccurence: OccurenceIdentifier? = null
    var arguments = HashMap<String, String>()

    constructor(node: Node, app: RuleApp) : this() {
        ruleName = app.rule().displayName()
        nodeId = NodeIdentifier.get(node)
        this.posInOccurence = OccurenceIdentifier.get(app.posInOccurrence())
        if (app is TacletApp) {
            /*SequentFormula seqForm = pos.getPosInOccurrence().sequentFormula();
                String sfTerm = LogicPrinter.quickPrintTerm(seqForm.formula(), services);
                String onTerm = LogicPrinter.quickPrintTerm(pos.getPosInOccurrence().subTerm(), services);
                sb.append("\n    formula=`").append(sfTerm).append("`");
                sb.append("\n    on=`").append(onTerm).append("`");
                sb.append("\n    occ=?;");
                */
            val iter = app.instantiations().pairIterator()
            while (iter.hasNext()) {
                val entry = iter.next()
                val p = entry.key().toString()

                val inst = entry.value().instantiation
                val v: String

                if (inst is Term) {
                    v = LogicPrinter.quickPrintTerm(inst, null)
                } else {
                    v = inst.toString()
                }

                arguments[p] = v
            }
        }
    }

    override val markdown: String
        get() {
            val formula = posInOccurence
            val parameters =
                    arguments.map { (key, value) -> "* $key : `$value`" }
                            .joinToString("\n")

            return """
            ## Rule `$ruleName` applied
            
            **Date**:             $created
            
            * Applied on `$formula`
            * The used parameter for the taclet instantation are 
            $parameters 
            
            """.trimIndent()
        }

    override val proofScriptRepresentation: String
        get() {
            val args = arguments.forEach { (k, v) ->
                "     inst_${firstWord(k)} = \"${v.trim { it <= ' ' }}\"\n"
            }

            return """
            rule $ruleName
                 on = ${posInOccurence?.term}
                 formula = ${posInOccurence?.toplevelTerm}
                 $args;
            """.trimIndent()
        }

    override fun toString(): String {
        return ruleName ?: "n/a"
    }

    private fun firstWord(k: String): String {
        val t = k.trim { it <= ' ' }
        val p = t.indexOf(' ')
        return if (p <= 0)
            t
        else
            t.substring(0, p)
    }

    @Throws(Exception::class)
    override fun reapplyStrict(uic: AbstractMediatorUserInterfaceControl, goal: Goal) {
        val ruleCommand = RuleCommand()
        val state = EngineState(goal.proof())
        val parameter: RuleCommand.Parameters?
        try {
            parameter = ruleCommand.evaluateArguments(state, arguments)
            ruleCommand.execute(uic, parameter, state)
        } catch (e: Exception) {
            throw IllegalStateException("Rule application", e)
        }

    }

    companion object {
        private val serialVersionUID = -3178292652264875668L
    }
}
