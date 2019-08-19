package edu.kit.iti.formal.psdbg.storage;


import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (16.05.18)
 */
@Data
@AllArgsConstructor
@NoArgsConstructor
public class PersistentState {
    private List<PersistentGoal> goals = new ArrayList<>();
}

