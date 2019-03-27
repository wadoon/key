package edu.kit.iti.formal.psdbg.storage;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;
import lombok.RequiredArgsConstructor;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.18)
 */
@Data
@AllArgsConstructor
@NoArgsConstructor
@XmlRootElement(name = "psdbg-state")
@XmlAccessorType(XmlAccessType.FIELD)
public class PersistentState {
    @XmlElement(name = "goal")
    private List<PersistentGoal> goals = new ArrayList<>();


}

