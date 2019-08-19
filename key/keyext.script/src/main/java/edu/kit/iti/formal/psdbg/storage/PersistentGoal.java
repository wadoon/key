package edu.kit.iti.formal.psdbg.storage;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;

@Data
@AllArgsConstructor
@NoArgsConstructor
public class PersistentGoal {
    private String goalIdentifier;
    private boolean selected = false;
    private List<PersistentVariable> variables = new ArrayList<>();

    public void addVariable(String identifier, String type, String value) {
        variables.add(new PersistentVariable(identifier, type, value));
    }
}
