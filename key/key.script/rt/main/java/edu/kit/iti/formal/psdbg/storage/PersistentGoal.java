package edu.kit.iti.formal.psdbg.storage;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import java.util.ArrayList;
import java.util.List;

@Data
@AllArgsConstructor
@NoArgsConstructor
@XmlAccessorType(XmlAccessType.FIELD)
public class PersistentGoal {
    @XmlAttribute(name = "id")
    public String goalIdentifier;

    @XmlAttribute(name = "selected")
    private boolean selected = false;

    @XmlElement
    private List<PersistentVariable> variables = new ArrayList<>();

    public void addVariable(String identifier, String type, String value) {
        variables.add(new PersistentVariable(identifier, type, value));
    }
}
