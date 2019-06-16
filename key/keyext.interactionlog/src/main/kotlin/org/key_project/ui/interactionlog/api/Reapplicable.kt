package org.key_project.ui.interactionlog.api

import de.uka.ilkd.key.gui.WindowUserInterfaceControl
import de.uka.ilkd.key.proof.Goal
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl

/**
 * @author Alexander Weigl
 * @version 1 (08.05.19)
 */
interface Reapplicable {
    @Throws(Exception::class)
    open fun reapply(uic: AbstractMediatorUserInterfaceControl, goal: Goal) {
        throw UnsupportedOperationException()
    }
}
