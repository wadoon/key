package org.key_project.machlearning;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.ui.MediatorProofControl;

public class AIKeYMain {

    public static void main(String[] args) {
        MediatorProofControl.PROVER_CORE_CLASS = AIProverCore.class;
        Main.main(args);
    }
}
