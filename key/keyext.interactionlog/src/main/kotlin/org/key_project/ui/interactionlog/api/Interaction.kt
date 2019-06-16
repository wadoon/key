package org.key_project.ui.interactionlog.api

import org.key_project.ui.interactionlog.api.Markdownable
import org.key_project.ui.interactionlog.api.Reapplicable
import org.key_project.ui.interactionlog.api.Scriptable

import javax.swing.*
import javax.xml.bind.annotation.XmlAccessType
import javax.xml.bind.annotation.XmlAccessorType
import javax.xml.bind.annotation.XmlAttribute
import javax.xml.bind.annotation.XmlTransient
import java.awt.*
import java.io.Serializable
import java.util.Date

/**
 * @author weigl
 */
@XmlTransient
@XmlAccessorType(XmlAccessType.FIELD)
abstract class Interaction : Serializable, Markdownable, Scriptable, Reapplicable {
    @XmlTransient
    var graphicalStyle = InteractionGraphicStyle()
        protected set

    @XmlAttribute
    var created = Date()

    @XmlAttribute
    var isFavoured = false

    class InteractionGraphicStyle {
        var icon: Icon? = null
        var backgroundColor: Color? = null
        var foregroundColor: Color? = null
    }
}
