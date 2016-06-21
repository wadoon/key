package org.key_project.common.core.logic;

import org.key_project.common.core.program.CCSourceElement;
import org.key_project.common.core.program.NameAbstractionTable;


public interface ModalContent {

    /**
     * returns true if the program is empty
     * @return true if empty
     */
    boolean isEmpty();

    /**
     * TODO: Document.
     *
     * @param se
     * @param nat
     * @return
     */
    boolean equalsModRenaming(Object se, NameAbstractionTable<? extends CCSourceElement> nat);
}