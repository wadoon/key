package org.key_project.ui.interactionlog.api

import org.key_project.ui.interactionlog.api.Interaction

interface InteractionRecorderListener {
    fun onInteraction(event: Interaction)
}
