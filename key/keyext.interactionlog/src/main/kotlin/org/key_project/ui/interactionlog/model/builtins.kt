package org.key_project.ui.interactionlog.model

import de.uka.ilkd.key.gui.WindowUserInterfaceControl
import de.uka.ilkd.key.proof.Goal
import de.uka.ilkd.key.proof.Node
import de.uka.ilkd.key.rule.*
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp
import de.uka.ilkd.key.smt.RuleAppSMT

object BuiltInRuleInteractionFactory {
    fun <T : IBuiltInRuleApp> create(node: Node, app: T): BuiltInRuleInteraction {
        return when (app) {
            is OneStepSimplifierRuleApp -> OSSBuiltInRuleInteraction(app, node)
            is ContractRuleApp -> ContractBuiltInRuleInteraction(app, node)
            is UseDependencyContractApp -> UseDependencyContractBuiltInRuleInteraction(app, node)
            is LoopContractInternalBuiltInRuleApp -> LoopContractInternalBuiltInRuleInteraction(app, node)
            is LoopInvariantBuiltInRuleApp -> LoopInvariantBuiltInRuleInteraction(app, node)
            is MergeRuleBuiltInRuleApp -> MergeRuleBuiltInRuleInteraction(app, node)
            is RuleAppSMT -> SMTBuiltInRuleInteraction(app, node)
            else -> throw IllegalArgumentException()
        }
    }
}


sealed class BuiltInRuleInteraction : NodeInteraction() {
    var ruleName: String? = null

    companion object {
        private val serialVersionUID = -4704080776691885200L
    }
}

/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
class ContractBuiltInRuleInteraction : BuiltInRuleInteraction {
    constructor()

    constructor(app: ContractRuleApp, node: Node)
}


/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
class LoopContractInternalBuiltInRuleInteraction : BuiltInRuleInteraction {

    constructor()

    constructor(app: LoopContractInternalBuiltInRuleApp, node: Node)
}


/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
class LoopInvariantBuiltInRuleInteraction(app: LoopInvariantBuiltInRuleApp, node: Node) : BuiltInRuleInteraction()


/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */

class MergeRuleBuiltInRuleInteraction : BuiltInRuleInteraction {

    constructor()

    constructor(app: MergeRuleBuiltInRuleApp, node: Node)
}


/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */

class OSSBuiltInRuleInteraction() : BuiltInRuleInteraction() {

    var occurenceIdentifier: OccurenceIdentifier? = null
    var nodeIdentifier: NodeIdentifier? = null

    override val markdown: String
        get() = String.format("## One step simplification%n" + "* applied on %n  * Term:%s%n  * Toplevel %s%n",
                occurenceIdentifier?.term,
                occurenceIdentifier?.toplevelTerm)

    override val proofScriptRepresentation: String
        get() = String.format("one_step_simplify %n" +
                "\t     on = \"%s\"%n" +
                "\tformula = \"%s\"%n;%n",
                occurenceIdentifier?.term,
                occurenceIdentifier?.toplevelTerm
        )

    constructor(app: OneStepSimplifierRuleApp, node: Node) : this() {
        nodeIdentifier = NodeIdentifier.get(node)
        occurenceIdentifier = OccurenceIdentifier.get(app.posInOccurrence())
    }

    override fun toString(): String {
        return "one step simplification on" + occurenceIdentifier?.term
    }

    @Throws(Exception::class)
    fun reapply(uic: WindowUserInterfaceControl, goal: Goal) {
        val oss = OneStepSimplifier()
        val pio = occurenceIdentifier!!.rebuildOn(goal)
        val app = oss.createApp(pio, goal.proof().services)
        goal.apply(app)
    }
}


/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
class SMTBuiltInRuleInteraction : BuiltInRuleInteraction {

    constructor()

    constructor(app: RuleAppSMT, node: Node)
}


/**
 * @author Alexander Weigl
 * @version 1 (09.12.18)
 */
class UseDependencyContractBuiltInRuleInteraction : BuiltInRuleInteraction {

    constructor()

    constructor(app: UseDependencyContractApp, node: Node)
}
