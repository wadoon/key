package org.key_project.ui.interactionlog

import org.key_project.ui.interactionlog.api.Interaction
import org.key_project.ui.interactionlog.model.*
import java.io.File
import javax.xml.bind.JAXBContext
import javax.xml.bind.JAXBException
import javax.xml.bind.Marshaller

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
object InteractionLogFacade {
    /**
     *
     */
    @JvmStatic
    val INTERACTIONS_CLASSES = arrayListOf(
            InteractionLog::class.java,
            AutoModeInteraction::class.java,
            NodeInteraction::class.java,
            MacroInteraction::class.java,
            SettingChangeInteraction::class.java,
            UserNoteInteraction::class.java,
            BuiltInRuleInteraction::class.java,
            ContractBuiltInRuleInteraction::class.java,
            LoopContractInternalBuiltInRuleInteraction::class.java,
            MergeRuleBuiltInRuleInteraction::class.java,
            OSSBuiltInRuleInteraction::class.java,
            SMTBuiltInRuleInteraction::class.java,
            //UseDependencyContractBuiltInRuleInteraction1::class.java,
            PruneInteraction::class.java,
            RuleInteraction::class.java,
            NodeIdentifier::class.java,
            Interaction::class.java
    )

    @JvmStatic
    @Throws(JAXBException::class)
    fun createContext(): JAXBContext {
        return JAXBContext.newInstance(*INTERACTIONS_CLASSES.toArray(arrayOf<Class<*>>()))
    }

    /**
     * @param inputFile
     * @return
     * @throws JAXBException
     */
    @JvmStatic
    @Throws(JAXBException::class)
    fun readInteractionLog(inputFile: File): InteractionLog {
        val ctx = createContext()
        val unmarshaller = ctx.createUnmarshaller()
        return unmarshaller.unmarshal(inputFile) as InteractionLog
    }

    /**
     * @param log
     * @param output
     * @throws JAXBException
     */
    @JvmStatic
    @Throws(JAXBException::class)
    fun storeInteractionLog(log: InteractionLog, output: File) {
        val ctx = createContext()
        val marshaller = ctx.createMarshaller()
        marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, java.lang.Boolean.TRUE)
        marshaller.marshal(log, output)
    }
}
