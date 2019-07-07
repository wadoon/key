package org.key_project.ui.interactionlog

import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.databind.SerializationFeature
import org.key_project.ui.interactionlog.model.InteractionLog
import java.io.File


/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
object InteractionLogFacade {

    val mapper = ObjectMapper().also {
        it.enable(SerializationFeature.INDENT_OUTPUT)
        //it.configure(JsonParser.Feature.ALLOW_COMMENTS, true)
        //it.configure(JsonParser.Feature.ALLOW_UNQUOTED_FIELD_NAMES, true)
        //it.configure(JsonParser.Feature.ALLOW_SINGLE_QUOTES, true)
        //it.configure(JsonGenerator.Feature.ESCAPE_NON_ASCII, true)
        /*it.registerSubtypes(
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
                Interaction::class.java)
         */
    }


    /**
     * @param inputFile
     * @return
     * @throws JAXBException
     */
    @JvmStatic
    fun readInteractionLog(inputFile: File): InteractionLog {
        return mapper.readValue(inputFile, InteractionLog::class.java)
    }

    /**
     * @param log
     * @param output
     * @throws JAXBException
     */
    @JvmStatic
    fun storeInteractionLog(log: InteractionLog, output: File) {
        mapper.writeValue(output, log)
    }
}
