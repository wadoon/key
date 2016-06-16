package org.key_project.common.core.logic;

import org.key_project.common.core.program.CCNameAbstractionTable;

public interface ModalContent<S/* program AST */, N extends CCNameAbstractionTable<S>> {

    /**
     * returns true if the program is empty
     * @return true if empty
     */
    boolean isEmpty();

    boolean equalsModRenaming(Object modalContent, N nat);

}