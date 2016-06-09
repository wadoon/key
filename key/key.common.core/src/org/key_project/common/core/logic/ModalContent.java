package org.key_project.common.core.logic;

import org.key_project.common.core.program.GenericNameAbstractionTable;

public interface ModalContent<S> {

    /**
     * returns true if the program is empty
     * @return true if empty
     */
    boolean isEmpty();

    boolean equalsModRenaming(Object modalContent, GenericNameAbstractionTable<S> nat);

}